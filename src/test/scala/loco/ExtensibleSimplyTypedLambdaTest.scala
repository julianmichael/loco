package loco

import org.scalatest.FunSuite

class ExtensibleSimplyTypedLambdaTest extends FunSuite {
  import ExtensibleSimplyTypedLambda._

  test("basic functionality") {
    val g = GlobalExpSpec(List(
      VarSpec,
      FuncSpec,
      BoolSpec,
      CondSpec,
      ProdSpec))
  }
}