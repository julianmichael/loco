package loco

import molt.syntax.cfg.parsable._
import molt.syntax.cfg._
import CFGParserHelpers._


object ExtensibleSimplyTypedLambdaParsing {
  import ExtensibleSimplyTypedLambda._
  object VarCategory extends RegexLexicalCategory("[a-zA-Z][a-zA-Z0-9]*")
  object IntCategory extends RegexLexicalCategory("[0-9]+")

  def makeExpParser(g: GlobalExpSpec): ComplexCFGParsable[g.Exp] = {

    def expProductionForSpec(spec: ExpSpec): (List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])) = (
      List(spec.expParser) -> ((c: List[AST[CFGParsable[_]]]) => for {
        e <- spec.expParser.fromAST(c(0))
      } yield g.makeExp(spec)(e)))

    val globalExpParser = new ComplexCFGParsable[g.Exp] {
      final override lazy val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])] = Map(
        List(Parenthesize(this)) -> ((c: List[AST[CFGParsable[_]]]) => for {
            t <- Parenthesize(this).fromAST(c(0))
          } yield t)
      ) ++ (for (spec <- g.expSpecs) yield expProductionForSpec(spec))
    }

    globalExpParser
  }

  def makeTypeParser(g: GlobalExpSpec): ComplexCFGParsable[g.Type] = {

    def typeProductionForSpec(spec: ExpSpec): Option[(List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Type]))] = spec.typeParser map { tParser =>
      List(tParser) -> ((c: List[AST[CFGParsable[_]]]) => for {
        e <- tParser.fromAST(c(0))
      } yield g.makeType(spec)(e))
    }

    val globalTypeParser = new ComplexCFGParsable[g.Type] {
      final override lazy val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Type])] = Map(
        List(Parenthesize(this)) -> ((c: List[AST[CFGParsable[_]]]) => for {
            t <- Parenthesize(this).fromAST(c(0))
          } yield t)
      ) ++ (for {
        spec <- g.expSpecs
        prod <- typeProductionForSpec(spec)
      } yield prod)
    }
    globalTypeParser
  }

  def makeVarExpParser(spec: VarSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(VarCategory) -> (c => for {
        v <- VarCategory.fromAST(c(0))
      } yield spec.Var(v))
    )
  }

  def makeUnitExpParser(spec: UnitSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("()")) -> (c => for {
        v <- Terminal("()").fromAST(c(0))
      } yield spec.Unit)
    )
  }

  def makeUnitTypeParser(spec: UnitSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(Terminal("Unit")) -> (c => for {
        v <- Terminal("Unit").fromAST(c(0))
      } yield spec.TUnit)
    )
  }


  def makeFuncExpParser(spec: FuncSpec): ComplexCFGParsable[spec.E] =
      new ComplexCFGParsable[spec.E] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.E])] = Map(
      List(Terminal("\\"), VarCategory, Terminal(":"), spec.g.typeParser, Terminal("."), spec.g.expParser) -> (c => for {
        p <- VarCategory.fromAST(c(1))
        typ <- spec.g.typeParser.fromAST(c(3))
        t <- spec.g.expParser.fromAST(c(5))
      } yield spec.Lam(p, typ, t)),
      List(spec.g.expParser, spec.g.expParser) -> (c => for {
        t1 <- spec.g.expParser.fromAST(c(0))
        t2 <- spec.g.expParser.fromAST(c(1))
      } yield spec.App(t1, t2))
    )
  }

  def makeFuncTypeParser(spec: FuncSpec): ComplexCFGParsable[spec.T] =
      new ComplexCFGParsable[spec.T] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.T])] = Map(
      List(spec.g.typeParser, Terminal("->"), spec.g.typeParser) -> (c => for {
        t1 <- spec.g.typeParser.fromAST(c(0))
        t2 <- spec.g.typeParser.fromAST(c(2))
      } yield spec.TFunc(t1,t2))
    )
  }
}