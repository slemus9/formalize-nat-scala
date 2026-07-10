package utils

object EqUtils:

  inline def show[A, B](eq: A =:= B): String =
    s"${TypeName[A]} =:= ${TypeName[B]}"
