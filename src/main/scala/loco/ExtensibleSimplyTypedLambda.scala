package loco

object ExtensibleSimplyTypedLambda {
  // In this file, I try to solve the Expression Problem.
  // I don't expect it to work.

  // Simply-typed lambda calculus with functions, products,
  // conditionals, unit, and bools.
  // Call-by-value.
  // ints were too much extra code; should just be included later
  // in the "extensible" variant that is to follow.
  // coproducts require those pesky annotations
  // because we don't have subtyping/Top or type inference
  // so I decided to nix them too.


  case class TypeError(message: String)

  // TODO fix this issue
  sealed trait Type
  case class TFunc(a: Type, b: Type) extends Type
  case class TProd(a: Type, b: Type) extends Type
  // case class TSum(a: Type, b: Type) extends Type
  case object TUnit extends Type
  case object TBool extends Type
  // case object TInt extends Type

  type TypeCheck = Either[TypeError, Type]
  type Environment = Map[String, Type]

  abstract class GlobalExpSpec(
    expSpecMakers: List[(GlobalExpSpec => ExpSpec)]) {

    val expSpecs = expSpecMakers.map(_.apply(this))

    // this crazy thing is to work around the fact that
    // constructors can't have dependent method types
    sealed trait Exp {
      val expSpec: ExpSpec
      val exp: expSpec.E
      override def toString: String = expSpec.toString(exp)
    }
    def makeExp(thisExpSpec: ExpSpec)(thisExp: thisExpSpec.E) = new Exp {
      val expSpec = thisExpSpec
      // compiler couldn't tell that expSpec == thisExpSpec
      // hopefully this will run ok
      val exp = thisExp.asInstanceOf[expSpec.E]
    }

    sealed trait Type {
      val expSpec: ExpSpec
      val typ: expSpec.T
    }
    def makeType(thisExpSpec: ExpSpec)(thisType: thisExpSpec.T) = new Type {
      val expSpec = thisExpSpec
      val typ = thisType.asInstanceOf[expSpec.T]
    }
    type TypeCheck = Either[TypeError, Type]
    type Environment = Map[String, Type]

    def isValue(e: Exp): Boolean = e.expSpec.isValue(e.exp)
    def freeVars(e: Exp): Set[String] = e.expSpec.freeVars(e.exp)
    def isClosed(t: Exp): Boolean = freeVars(t).isEmpty
    // the unfortunate casts WILL be accurate because of
    // the appropriate things being equal
    def substitute(sub: Exp, name: String, target: Exp): Exp = {
      target.expSpec.substitute(
        sub.asInstanceOf[target.expSpec.g.Exp],
        name,
        target.exp).asInstanceOf[Exp]
    }
    def typeof(t: Exp): TypeCheck = typeWithEnv(Map.empty[String, Type], t)
    def typeWithEnv(env: Environment, t: Exp): TypeCheck =
      t.expSpec.typeWithEnv(
        env.asInstanceOf[t.expSpec.g.Environment],
        t.exp
      ).asInstanceOf[TypeCheck]

    def step(t: Exp): Exp =
      if(isValue(t)) t
      else t.expSpec.step(t.exp).asInstanceOf[Exp]

    def smallStepEval(t: Exp): Either[TypeError, Exp] = for {
      _ <- typeof(t).right
    } yield {
      var term = t
      var nextTerm = step(t)
      while(term != nextTerm) {
        term = nextTerm
        nextTerm = step(nextTerm)
      }
      term
    }
  }

  abstract class ExpSpec(val g: GlobalExpSpec) {
    type E // the type of expressions
    type T // the type of the new types

    // convenience method
    def makeExp(e: E): g.Exp = g.makeExp(this)(e)
    def makeType(t: T): g.Type = g.makeType(this)(t)

    def isValue(e: E): Boolean
    def freeVars(e: E): Set[String]
    def substitute(sub: g.Exp, name: String, target: E): g.Exp

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck

    def step(t: E): g.Exp

    def toString(e: E): String
  }

  case class VarSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    case class Var(x: String)
    type E = Var
    type T = g.Type

    def isValue(e: E): Boolean = false

    def freeVars(e: E): Set[String] = e match {
      case Var(name) => Set(name)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = target match {
      case Var(y) if y == name => sub
      case v@Var(_) => g.makeExp(this)(v)
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Var(x) => env.get(x) match {
        case Some(typ) => Right(typ)
        case None => Left(TypeError(s"free variable $x"))
      }
    }

    def step(t: E): g.Exp = ???

    override def toString(e: E): String = e match { case Var(x) => x }
  }

  case class FuncSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    // TODO depends on Var
    private[this] val innerVarSpec = VarSpec(g)
    sealed trait FuncTerm
    case class Lam(param: String, paramType: g.Type, body: g.Exp) extends FuncTerm
    case class App(t1: g.Exp, t2: g.Exp) extends FuncTerm

    case class TFunc(a: g.Type, b: g.Type)

    type E = FuncTerm
    type T = TFunc

    def isValue(e: E): Boolean = e match {
      case Lam(_, _, _) => true
      case App(_, _) => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Lam(param, typ, body) => g.freeVars(body) - param
      case App(t1, t2) => g.freeVars(t1) ++ g.freeVars(t2)
    }

    private[this] def alpha(prohib: Set[String], lam: Lam): Lam = lam match {
      case Lam(param, typ, t) if(prohib(param)) =>
        val newVar = freshVar(prohib)
        Lam(newVar, typ,
          g.substitute(g.makeExp(innerVarSpec)(innerVarSpec.Var(newVar)), param, t))
      case x => x
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case l@Lam(_, _, _) =>
          val Lam(newP, typ, newT) = alpha(g.freeVars(sub) ++ freeVars(l), l)
          makeExp(Lam(newP, typ, doSub(newT)))
        case App(t1, t2) => g.makeExp(this)(App(doSub(t1), doSub(t2)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Lam(p, typ, body) => for {
        returnType <- g.typeWithEnv(env + (p -> typ), body).right
      } yield makeType(TFunc(typ, returnType))
      case App(t1, t2) => for {
        apperType <- g.typeWithEnv(env, t1).right
        appeeType <- g.typeWithEnv(env, t2).right
        resultType <- (apperType.typ match {
          case TFunc(ante, consq) if ante == appeeType => Right(consq)
          case x => Left(TypeError(s"tried to apply type $x to $appeeType"))
        }).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case App(t1, t2) if !g.isValue(t1) => makeExp(App(g.step(t1), t2))
      case App(v1, t2) if !g.isValue(t2) => makeExp(App(v1, g.step(t2)))
      case App(v1, v2) => v1.exp match {
        case Lam(p, _, t) => g.substitute(v2, p, t)
      }
    }

    override def toString(e: E): String = e match {
      case Lam(p, typ, body) => s"(\\$p: $typ. $body)"
      case App(t1, t2) => s"($t1 $t2)"
    }
  }

  case class BoolSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    sealed trait BoolExp
    case class BoolLiteral(b: Boolean) extends BoolExp
    case class And(a: g.Exp, b: g.Exp) extends BoolExp
    case class Or(a: g.Exp, b: g.Exp) extends BoolExp

    object TBool

    type E = BoolExp
    type T = TBool.type

    def isValue(e: E): Boolean = e match {
      case BoolLiteral(_) => true
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case BoolLiteral(_) => Set.empty[String]
      case And(a, b) => g.freeVars(a) ++ g.freeVars(b)
      case Or(a, b) => g.freeVars(a) ++ g.freeVars(b)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case b@BoolLiteral(_) => makeExp(b)
        case And(a, b) => makeExp(And(doSub(a), doSub(b)))
        case Or(a, b) => makeExp(Or(doSub(a), doSub(b)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case b@BoolLiteral(_) => Right(makeType(TBool))
      case And(l, r) => for {
        leftType <- g.typeWithEnv(env, l).right
        rightType <- g.typeWithEnv(env, r).right
        result <- (if(leftType.typ == TBool && rightType.typ == TBool) Right(makeType(TBool))
                  else Left(TypeError(s"tried to && terms of type $leftType and $rightType"))).right
      } yield result
      case Or(l, r) => for {
        leftType <- g.typeWithEnv(env, l).right
        rightType <- g.typeWithEnv(env, r).right
        result <- (if(leftType.typ == TBool && rightType.typ == TBool) Right(makeType(TBool))
                  else Left(TypeError(s"tried to || terms of type $leftType and $rightType"))).right
      } yield result
    }

    def step(t: E): g.Exp = makeExp(t match {
      case And(t1, t2) if !g.isValue(t1) => And(g.step(t1), t2)
      case And(v1, t2) if !g.isValue(t2) => And(v1, g.step(t2))
      case And(v1, v2) => (v1.exp, v2.exp) match {
        case (BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 && b2)
      }
      case Or(t1, t2) if !g.isValue(t1) => Or(g.step(t1), t2)
      case Or(v1, t2) if !g.isValue(t2) => Or(v1, g.step(t2))
      case Or(v1, v2) => (v1.exp, v2.exp) match {
        case (BoolLiteral(b1), BoolLiteral(b2)) => BoolLiteral(b1 || b2)
    }
    })

    def toString(e: E): String = e match {
      case BoolLiteral(b) => s"$b"
      case And(a, b) => s"$a && $b"
      case Or(a, b) => s"$a || $b"
    }
  }

  case class CondSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    // TODO depends on bool
    private[this] val innerBoolSpec = BoolSpec(g)
    case class Cond(cond: g.Exp, body: g.Exp, otherwise: g.Exp)

    type E = Cond
    type T = g.Type

    def isValue(e: E): Boolean = false

    def freeVars(e: E): Set[String] = e match {
      case Cond(c, b, ow) => g.freeVars(c) ++ g.freeVars(b) ++ g.freeVars(ow)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match { case Cond(c, b, ow) =>
        makeExp(Cond(doSub(c), doSub(b), doSub(ow)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Cond(cond, body, ow) => for {
        condType <- g.typeWithEnv(env, cond).right
        _ <- (if(condType.typ == innerBoolSpec.TBool) Right(condType)
          else Left(TypeError(s"condition $cond not of type Bool"))).right
        bodyType <- g.typeWithEnv(env, body).right
        elseType <- g.typeWithEnv(env, ow).right
        resultType <- (if(bodyType == elseType) Right(bodyType)
          else Left(TypeError(s"mismatched types in if-else: $bodyType and $elseType"))).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case Cond(cond, body, ow) if !g.isValue(cond) =>
        makeExp(Cond(g.step(cond), body, ow))
      case Cond(v, body, ow) => v.exp match {
        case innerBoolSpec.BoolLiteral(true) => body
        case innerBoolSpec.BoolLiteral(false) => ow
      }
    }

    def toString(e: E): String = e match {
      case Cond(c, b, ow) => s"if $c then $b else $ow"
    }
  }

  case class ProdSpec(override val g: GlobalExpSpec) extends ExpSpec(g) {
    sealed trait ProdExp
    case class Pair(t1: g.Exp, t2: g.Exp) extends ProdExp
    case class Pi1(t: g.Exp) extends ProdExp
    case class Pi2(t: g.Exp) extends ProdExp

    case class TProd(l: g.Type, r: g.Type)

    type E = ProdExp
    type T = TProd

    def isValue(e: E): Boolean = e match {
      case Pair(v1, v2) => g.isValue(v1) && g.isValue(v2)
      case _ => false
    }

    def freeVars(e: E): Set[String] = e match {
      case Pair(t1, t2) => g.freeVars(t1) ++ g.freeVars(t2)
      case Pi1(t) => g.freeVars(t)
      case Pi2(t) => g.freeVars(t)
    }

    def substitute(sub: g.Exp, name: String, target: E): g.Exp = {
      def doSub(x: g.Exp) = g.substitute(sub, name, x)
      target match {
        case Pair(t1, t2) => makeExp(Pair(doSub(t1), doSub(t2)))
        case Pi1(t) => makeExp(Pi1(doSub(t)))
        case Pi2(t) => makeExp(Pi2(doSub(t)))
      }
    }

    def typeWithEnv(env: g.Environment, t: E): g.TypeCheck = t match {
      case Pair(t1, t2) => for {
        leftType <- g.typeWithEnv(env, t1).right
        rightType <- g.typeWithEnv(env, t2).right
      } yield makeType(TProd(leftType, rightType))
      case Pi1(t) => for {
        innerType <- g.typeWithEnv(env, t).right
        resultType <- (innerType.typ match {
          case TProd(l, r) => Right(l)
          case x => Left(TypeError(s"projection π1 operating on type $x"))
        }).right
      } yield resultType
      case Pi2(t) => for {
        innerType <- g.typeWithEnv(env, t).right
        resultType <- (innerType.typ match {
          case TProd(l, r) => Right(r)
          case x => Left(TypeError(s"projection π2 operating on type $x"))
        }).right
      } yield resultType
    }

    def step(t: E): g.Exp = t match {
      case Pair(t1, t2) if !g.isValue(t1) => makeExp(Pair(g.step(t1), t2))
      case Pair(v1, t2) if !g.isValue(t2) => makeExp(Pair(v1, g.step(t2)))
      case Pi1(t) if !g.isValue(t) => makeExp(Pi1(g.step(t)))
      case Pi1(v) => v.exp match { case Pair(v1, v2) => v1 }
      case Pi2(t) if !g.isValue(t) => makeExp(Pi2(g.step(t)))
      case Pi2(v) => v.exp match { case Pair(v1, v2) => v2 }
    }

    def toString(e: E): String = e match {
      case Pair(t1, t2) => s"($t1, $t2)"
      case Pi1(t) => s"π1 $t"
      case Pi2(t) => s"π2 $t"
    }
  }


  sealed trait Exp {
    override def toString: String = this match {
      /*
      case Inl(t) => s"inl $t"
      case Inr(t) => s"inr $t"
      case Case(t, lName, lBody, rName, rBody) =>
        s"case $t of (inl $lName => $lBody) (inr $rName => $rBody)"
      */
      case Unit => "()"
      /*
      case IntLiteral(i) => s"$i"
      case Plus(a, b) => s"$a + $b"
      case Minus(a, b) => s"$a - $b"
      case Times(a, b) => s"$a * $b"
      case Div(a, b) => s"$a / $b"
      */
    }
  }

  // coproducts
  /*
  case class Inl(t: Exp) extends Exp
  case class Inr(t: Exp) extends Exp
  case class Case(t: Exp, lName: String, lBody: Exp,
                          rName: String, rBody: Exp) extends Exp
  */
  // unit
  case object Unit extends Exp
  // ints
  /*
  case class IntLiteral(n: Int) extends Exp
  case class Plus(a: Exp, b: Exp) extends Exp
  case class Minus(a: Exp, b: Exp) extends Exp
  case class Times(a: Exp, b: Exp) extends Exp
  case class Div(a: Exp, b: Exp) extends Exp
  */

  def isValue(t: Exp): Boolean = t match {
    // case Inl(v) => isValue(v)
    // case Inr(v) => isValue(v)
    case Unit => true
    // case IntLiteral(_) => true
    case _ => false
  }

  /* Implement if I end up needing it
  def girth(t: Exp): Int = t match {
    case Var(_) => 1
    case Lam(_, t1) => 1 + girth(t1)
    case App(t1, t2) => 1 + girth(t1) + girth(t2)
  }

  def size(t: Exp): Int = t match {
    case Var(_) => 1
    case Lam(_, t1) => 1 + size(t1)
    case App(t1, t2) => 1 + math.max(girth(t1), girth(t2))
  }
  */

  def freeVars(t: Exp): Set[String] = t match {
    /*
    case Inl(t) => freeVars(t)
    case Inr(t) => freeVars(t)
    case Case(t, lName, lBody, rName, rBody) =>
      freeVars(t) ++ freeVars(lBody) ++ freeVars(rBody)

    case Plus(a, b) => freeVars(a) ++ freeVars(b)
    case Minus(a, b) => freeVars(a) ++ freeVars(b)
    case Times(a, b) => freeVars(a) ++ freeVars(b)
    case Div(a, b) => freeVars(a) ++ freeVars(b)
    */
    // bool, int literals; unit
    case _ => Set.empty[String]
  }

  /*
  def alpha(prohib: Set[String], cas: Case): Case = cas match {
    case Case(t, lName, lBody, rName, rBody) =>
      val newName = freshVar(prohib)
      val (newLName, newLBody) =
        if(prohib(lName)) {
          (newName, substitute(Var(newName), lName, lBody))
        } else {
          (lName, lBody)
        }
      val (newRName, newRBody) =
        if(prohib(rName)) {
          (newName, substitute(Var(newName), rName, rBody))
        } else {
          (rName, rBody)
        }
      Case(t, newLName, newLBody, newRName, newRBody)
  }
  */

  // as of here I stopped trying to implement ints.

  // substitute `sub` for `name` in `target`
  def substitute(sub: Exp, name: String, target: Exp): Exp = {
    def doSub(x: Exp) = substitute(sub, name, x)
    target match {
      /*
      case Inl(t) => Inl(doSub(t))
      case Inr(t) => Inr(doSub(t))
      case c@Case(_, _, _, _, _) =>
        val Case(t, lName, lBody, rName, rBody) =
          alpha(freeVars(sub) ++ freeVars(c), c)
        Case(t, lName, doSub(lBody), rName, doSub(rBody))
      */
      case Unit => Unit
    }
  }

  // as of here I stopped trying to implement coproducts
  // (because I realized we need the annotations)

  def typeof(t: Exp): TypeCheck = typeWithEnv(Map.empty[String, Type], t)
  def typeWithEnv(env: Environment, t: Exp): TypeCheck = t match {
    case Unit => Right(TUnit)
  }

  /*
  def bigStepEval(t: Exp): Exp = t match {
    case v if isValue(v) => v
    case App(t1, t2) => {
      val v1 = bigStepEval(t1)
      val v2 = bigStepEval(t2)
      (v1: @unchecked) match {
        case Lam(p, t) => {
          println(s"$v1 $v2")
          bigStepEval(substitute(t, p, v2))
        }
        // otherwise we're stuck (free variable) or looping
      }
    }
  }

  def superEval(t: Exp): Exp = t match {
    case v@Var(_) => v
    case l@Lam(p, t1) => Lam(p, superEval(t1))
    case App(t1, t2) => {
      val v1 = superEval(t1)
      val v2 = superEval(t2)
      (v1: @unchecked) match {
        case Lam(p, tt) => superEval(substitute(tt, p, v2))
        case _ => App(v1, v2)
      }
    }
  }
  */
}
