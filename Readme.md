# Trying to Formalize Arithmetic in Plain Scala

This is a fun exercise to see if Scala's Type System would let me formalize some properties of the Peano Arithmetic, just like I would in a proof assistant language such as Agda or Coq.
Even though Scala's Type System is unsound, and hence it would be unreliable to use it as a proof assistant, I wanted to see if the Dependent Type Theory foundation that underlies Scala would let me write expressions that could be considered proofs under the Type Theory lens

I tried to do some proofs of the following statements:

```scala
type LeftUnit[N] = Zero.type + N =:= N

type RightUnit[N] = N + Zero.type =:= N

type LeftSuc[M, N] = Suc[M] + N =:= Suc[M + N]

type RightSuc[M, N] = M + Suc[N] =:= Suc[M + N]

type Commutative[M, N] = M + N =:= N + M
```

I relied on the built-in equality type (`=:=`) that's already in the language, and used Match Types to define addition (`+`) at the type level.
To build the proofs, I introduced another type that would let me "split" a natural number by cases:

```scala
enum NatCase[A]:
  /**
    * Asserts that A is equal to Zero
    */
  case ZeroCase[A](eq: A =:= Zero.type) extends NatCase[A]

  /**
    * Asserts that A is equal to Suc[N] for some N
    */
  case SucCase[A, N](eq: A =:= Suc[N], prev: NatCase[N]) extends NatCase[A]
```

I first tried to do the proofs using Match Types (which also guarantee termination), however I found them quite unwieldy for the task, so I opted for defining this helper type instead

## How to Run

This is a [scala-cli](https://scala-cli.virtuslab.org/) script. To run it you can execute the following command from outside the root of this project:

```
scala-cli formalize-nat-scala
```

The entry point is the `nat.sc` file
