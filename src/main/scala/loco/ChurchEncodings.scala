package loco

object ChurchEncodings {
  import PureLambda._
  type Exp = PureLambda
  val id = Lam("x", Var("x"))
  val mock = Lam("x", App(Var("x"), Var("x")))
  val tru = Lam("x", Lam("y", Var("x")))
  val fals = Lam("x", Lam("y", Var("y")))
  def nat(i: Int) = {
    var count = i
    var inside: Exp = Var("x")
    while(count > 0) {
      inside = App(Var("f"), inside)
      count -= 1
    }
    Lam("f", Lam("x", inside))
  }
  val plus = Lam("n", Lam("m", Lam("f", Lam("x", App(Var("m"), App(Var("f"),
                App(Var("n"), App(Var("f"), Var("x")))))))))
  val times = Lam("n", Lam("m", App(App(Var("m"), App(plus, Var("n"))), nat(0))))

  val abbreviations: Map[String, Exp] = Map(
    "true" -> tru,
    "false" -> fals,
    "id" -> id,
    "+" -> plus,
    "*" -> times
  )
}

