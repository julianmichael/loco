package loco

import org.scalatest.FunSuite

class SimplyTypedLambdaTest extends FunSuite {
  import SimplyTypedLambda._
  import SampleExps._

  test("isValue") {
    assert(isValue(id(TBool)) === true)
    assert(isValue(tru) === true)
    assert(isValue(App(id(TFunc(TBool, TBool)), id(TBool))) === false)
  }

  test("freeVars") {
    assert(freeVars(id(TBool)) === Set.empty[String])
    assert(freeVars(Var("x")) === Set("x"))
  }

  test("isClosed") {
    assert(isClosed(id(TBool)) === true)
  }

  //TODO alpha subst and other tests

  test("step") {
    assert(step(App(id(TFunc(TBool, TBool)), id(TBool))) === id(TBool))
  }

  test("smallStepEval") {
    assert(smallStepEval(
      App(id(TFunc(TBool, TBool)),
      App(id(TFunc(TBool, TBool)), id(TBool)))) === Right(id(TBool)))
  }

  // TODO big step eval and other tests
}