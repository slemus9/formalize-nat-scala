import scala.compiletime.erasedValue
import scala.compiletime.summonInline

import utils.TypeName
import utils.EqUtils

// ----------------------------------
// Natural Numbers and their operations
// ----------------------------------

/**
  * Notes:
  * 1) the transparent keyword helps me infer the most specific type when writing down expressions.
  * For example, if I inspect the type of the following expression:
  *
  * val three = Suc(Suc(Suc(Zero)))
  *
  * it would give me:
  *
  * three : Suc[Suc[Suc[Zero.type]]]
  *
  * 2) Suc[N] does not have any constraint enforcing that N should be a subtype of Nat.
  * I removed it because subtyping does not interact well with functions that receive higher-kinded types.
  *
  * For example, if I try to use the liftCo function from the A =:= B type:
  *
  * def liftCo[F[_]]: F[From] =:= F[To]
  *
  * (eq: N =:= M).liftCo[Suc]
  *
  * It will fail with the following error:
  *
  * Type argument nat$_.this.Suc does not conform to upper bound [_] =>> Any
  *
  * I do not think, however, that removing this constraint affects the validity of the proofs
  */
transparent sealed trait Nat
case object Zero extends Nat
final case class Suc[N](n: N) extends Nat

type Add[M, N] = M match
  case Zero.type => N
  case Suc[m] => Suc[Add[m, N]]

infix type +[M, N] = Add[M, N]

def add[M, N](m: M, n: N): Add[M, N] =
  m match
    case _: Zero.type => n
    case sm: Suc[m] => Suc(add(sm.n, n))

/**
  * Helper type to Split a Nat by cases
  */
enum NatCase[A]:
  /**
    * Asserts that A is equal to Zero
    */
  case ZeroCase[A](eq: A =:= Zero.type) extends NatCase[A]

  /**
    * Asserts that A is equal to Suc[N] for some N
    */
  case SucCase[A, N](eq: A =:= Suc[N], prev: NatCase[N]) extends NatCase[A]

object NatCase:

  inline def apply[A]: NatCase[A] =
    nat[A]

  inline given nat[A]: NatCase[A] =
    inline erasedValue[A] match
      case _: Zero.type => ZeroCase(summonInline[A =:= Zero.type])
      case _: Suc[n] => SucCase(summonInline[A =:= Suc[n]], nat[n])

// ----------------------------------
// Helper functions of the =:= type
// ----------------------------------

def refl[A]: A =:= A =
  summon

// ----------------------------------
// Properties of the Natural Numbers
// ----------------------------------

type LeftUnit[N] = Zero.type + N =:= N
def leftUnit[N]: LeftUnit[N] =
  refl

type RightUnit[N] = N + Zero.type =:= N
def rightUnit[N](using natCase: NatCase[N]): RightUnit[N] =
  natCase match
    case NatCase.ZeroCase(eq) =>
      val h1 = eq.liftCo[[X] =>> Add[X, Zero.type]]
      val h2 = h1.andThen(eq.flip)
      h2

    case sucCase: NatCase.SucCase[N, n] =>
      val ih = rightUnit[n](using sucCase.prev)
      val h1 = sucCase.eq.liftCo[[X] =>> Add[X, Zero.type]]
      val h2 = h1.andThen(ih.liftCo[Suc])
      val h3 = h2.andThen(sucCase.eq.flip)
      h3

type LeftSuc[M, N] = Suc[M] + N =:= Suc[M + N]
def leftSuc[M, N]: LeftSuc[M, N] =
  refl

type RightSuc[M, N] = M + Suc[N] =:= Suc[M + N]
def rightSuc[M, N](using natCase: NatCase[M]): RightSuc[M, N] =
  natCase match
    /**
      *
      * If M =:= Zero:
      *
      *     M + Suc[N]
      * =:= Zero + Suc[N] (because M =:= Zero)
      * =:= Suc[Zero + N] (by _+_ definition)
      * =:= Suc[M + N]    (because M =:= Zero)
      */
    case NatCase.ZeroCase(eq) =>
      val h1 = eq.liftCo[[X] =>> X + Suc[N]]      // M + Suc[N] =:= Zero + Suc[N]
      val h2 = eq.flip.liftCo[[X] =>> Suc[X + N]] // Suc[Zero + N] =  Suc[M + N]
      h1.andThen(h2)

    /**
      * If M =:= Suc[m]:
      *
      * Inductive Hypothesis: m + Suc[N] =:= Suc[m + N]
      *
      *     M + Suc[N]
      * =:= Suc[m] + Suc[N] (because M =:= Suc[m])
      * =:= Suc[m + Suc[N]] (by _+_ definition)
      * =:= Suc[Suc[m + N]] (by Inductive Hypothesis)
      * =:= Suc[Suc[m] + N] (by _+_ definition)
      * =:= Suc[M + N]      (because M =:= Suc[m])
      */
    case sucCase: NatCase.SucCase[M, m] =>
      val h1 = sucCase.eq.liftCo[[X] =>> X + Suc[N]]      // M + Suc[N] =:= Suc[m + Suc[N]]
      val ih = rightSuc[m, N](using sucCase.prev)         // m + Suc[N] =:= Suc[m + N]
      val h2 = sucCase.eq.flip.liftCo[[X] =>> Suc[X + N]] // Suc[Suc[m + N]] =:= Suc[M + N]
      h1.andThen(ih.liftCo[Suc]).andThen(h2)

type Commutative[M, N] = M + N =:= N + M
def commutative[M, N](using
    mCase: NatCase[M],
    nCase: NatCase[N]
): Commutative[M, N] =
  mCase match
    /**
      * If M =:= Zero:
      *
      *     M + N
      * =:= Zero + N (because M =:= Zero)
      * =:= N        (by _+_ definition)
      * =:= N + Zero (by rightUnit[N])
      * =:= N + M    (because M =:= Zero)
      */
    case NatCase.ZeroCase(eq) =>
      val h1 = eq.liftCo[[X] =>> X + N]      // M + N =:= N
      val h3 = rightUnit[N].flip             // N =:= N + Zero
      val h2 = eq.flip.liftCo[[X] =>> N + X] // N + Zero =:= N + M
      h1.andThen(h3).andThen(h2)

    /**
      * If M =:= Suc[m]:
      *
      * Inductive Hypothesis: m + N =:= N + m
      *
      *     M + N
      * =:= Suc[m] + N (because M =:= Suc[m])
      * =:= Suc[m + N] (by _+_ definition)
      * =:= Suc[N + m] (by Inductive Hypothesis)
      * =:= N + Suc[m] (By rightSuc[N, m])
      * =:= N + M      (because M =:= Suc[m])
      */
    case sucCase: NatCase.SucCase[M, m] =>
      val h1 = sucCase.eq.liftCo[[X] =>> X + N]             // M + N =:= Suc[m + N]
      val ih = commutative[m, N](using sucCase.prev, nCase) // m + N =:= N + m
      val h2 = rightSuc[N, m].flip                          // Suc[N + m] =:= N + Suc[m]
      val h3 = sucCase.eq.flip.liftCo[[X] =>> N + X]        // N + Suc[m] =:= N + M
      h1.andThen(ih.liftCo[Suc])
        .andThen(h2)
        .andThen(h3)

// ----------------------------------
// Some Examples
// ----------------------------------

type Four = Suc[Suc[Suc[Suc[Zero.type]]]]
type Three = Suc[Suc[Suc[Zero.type]]]
type Two = Suc[Suc[Zero.type]]
val four = Suc(Suc(Suc(Suc(Zero))))
val three = Suc(Suc(Suc(Zero)))
val two = Suc(Suc(Zero))
val five = add(four, three) // five : Suc[Suc[Suc[Suc[Suc[Zero.type]]]]]

// Printing some values to see if they terminate

println(NatCase[Four])
println(five)
println(EqUtils.show(leftUnit[Four]))
println(EqUtils.show(rightUnit[Four]))
println(EqUtils.show(leftSuc[Three, Two]))
println(EqUtils.show(rightSuc[Four, Four]))
println(EqUtils.show(commutative[Four, Three]))
