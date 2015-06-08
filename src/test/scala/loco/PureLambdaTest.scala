package loco

import org.scalatest.FunSuite

class PureLambdaTestSuite extends FunSuite {
  import PureLambda._
  import SampleExps._

  test("isValue") {
    assert(isValue(id) === true)
    assert(isValue(tru) === true)
    assert(isValue(App(id, id)) === false)
  }

  test("girth") {
    assert(girth(id) === 2)
    assert(girth(mock) === 4)
  }

  test("size") {
    assert(size(id) === 2)
    assert(size(mock) === 3)
  }

  test("freeVars") {
    assert(freeVars(id) === Set.empty[String])
    assert(freeVars(Var("x")) === Set("x"))
  }

  test("isClosed") {
    assert(isClosed(id) === true)
  }

  //TODO alpha subst and other tests

  test("step") {
    assert(step(App(id, App(id, id))) === App(id, id))
    assert(step(App(id, id)) === id)
  }

  test("smallStepEval") {
    assert(smallStepEval(App(id, App(id, id))) === id)
  }

  // TODO big step eval and other tests
}