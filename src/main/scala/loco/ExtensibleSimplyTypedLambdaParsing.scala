package loco

import molt.syntax.cfg.parsable._
import molt.syntax.cfg._
import CFGParserHelpers._


object ExtensibleSimplyTypedLambdaParsing {
  import ExtensibleSimplyTypedLambda._
  object VarCategory extends RegexLexicalCategory("[a-zA-Z][a-zA-Z0-9]*")
  object IntCategory extends RegexLexicalCategory("[0-9]+")

  def makeExpParser(g: GlobalExpSpec): ComplexCFGParsable[g.Exp] = {

    val childProductions = g.expSpecs.flatMap(
      _.parser.synchronousProductions.asInstanceOf[Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])]])

    val globalExpParser = new ComplexCFGParsable[g.Exp] {
      final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[g.Exp])] = Map(
        List(Parenthesize(this)) -> ((c: List[AST[CFGParsable[_]]]) => for {
            t <- Parenthesize(this).fromAST(c(0))
          } yield t)
      ) ++ childProductions
    }
    globalExpParser
  }

  def makeVarParser(spec: VarSpec): ComplexCFGParsable[spec.g.Exp] =
      new ComplexCFGParsable[spec.g.Exp] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.g.Exp])] = Map(
      List(VarCategory) -> (c => for {
        v <- VarCategory.fromAST(c(0))
      } yield spec.makeExp(spec.Var(v)))
    )
  }

  def makeUnitParser(spec: UnitSpec): ComplexCFGParsable[spec.g.Exp] =
      new ComplexCFGParsable[spec.g.Exp] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.g.Exp])] = Map(
      List(Terminal("()")) -> (c => for {
        v <- Terminal("()").fromAST(c(0))
      } yield spec.makeExp(spec.Unit))
    )
  }


  def makeFuncParser(spec: FuncSpec): ComplexCFGParsable[spec.g.Exp] =
      new ComplexCFGParsable[spec.g.Exp] {
    final override val synchronousProductions: Map[List[CFGParsable[_]], (List[AST[CFGParsable[_]]] => Option[spec.g.Exp])] = Map(
      List(Terminal("\\"), VarCategory, Terminal("."), spec.g.parser) -> (c => for {
        p <- VarCategory.fromAST(c(1))
        t <- spec.g.parser.fromAST(c(3))
      } yield spec.makeExp(spec.Lam(p, t))),
      List(spec.g.parser, spec.g.parser) -> (c => for {
        t1 <- spec.g.parser.fromAST(c(0))
        t2 <- spec.g.parser.fromAST(c(1))
      } yield spec.makeExp(spec.App(t1, t2)))
    )
  }
}