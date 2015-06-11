package loco

import org.scalatest.FunSuite

class ExtensibleSimplyTypedLambdaTest extends FunSuite {
  import ExtensibleSimplyTypedLambda._
  import molt.syntax.cfg.parsable.ParseCommands._

  test("basic functionality") {
    val g = GlobalExpSpec(List(
      VarSpec,
      FuncSpec,
      UnitSpec))
    implicit val parser = g.expParser
    type Exp = g.Exp
    val idUnit = parseUnique[Exp]("\\ x : Unit . x")
    println(idUnit)
  }
}