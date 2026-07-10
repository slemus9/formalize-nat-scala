package utils

import scala.quoted.*

object TypeName:
  inline def apply[A]: String = ${ showTypeName[A] }

  def showTypeName[A: Type](using Quotes): Expr[String] =
    Expr { Type.show[A] }
