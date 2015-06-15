package loco

import org.scalatest.FunSuite

class ExtensibleSimplyTypedLambdaTest extends FunSuite {
  import ExtensibleSimplyTypedLambda._
  import molt.syntax.cfg.parsable.ParseCommands._

  test("basic functionality") {
    val g = GlobalExpSpec(List(
      VarSpec,
      FuncSpec,
      UnitSpec,
      BoolSpec,
      IntSpec,
      CondSpec,
      ProdSpec,
      CoprodSpec
    ))
    implicit val parser = g.expParser
    type Exp = g.Exp
    val neg = parseForced[Exp]("(\\ x : Bool . !!x) False")
    def steps(e: Exp): Stream[Exp] = e #:: steps(g.step(e))
    println(g.smallStepEval(neg))
    // println(steps(neg).take(5).toList)
  }
}