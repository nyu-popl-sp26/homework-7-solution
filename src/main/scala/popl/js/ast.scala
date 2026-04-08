package popl.js

import popl.js.ast.fv
import popl.js.util.JsException

import scala.util.parsing.input.Positional

object ast:
  /* JakartaScript Type Expressions */
  enum Typ:
    // pretty print as AST
    override def toString: String = print.prettyAST(this)
    // pretty print as JS expression
    def pretty: String = print.prettyTyp(this)
  
    case TNumber
    case TBool
    case TString
    case TUndefined
    case TFunction(ts: Typ, tret: Typ)

  /* JakartaScript Expressions */
  sealed abstract class Expr extends Positional:
    // pretty print as AST
    override def toString: String = print.prettyAST(this)

    // pretty print as JS expression
    def prettyJS: String = print.prettyJS(this)

    // pretty print as value
    def prettyVal: String = print.prettyVal(this)
  end Expr


  /* Literals and Values */
  sealed abstract class Val extends Expr

  case class Num(n: Double) extends Val

  case class Bool(b: Boolean) extends Val

  case class Str(s: String) extends Val

  case object Undefined extends Val

  /* Variables */
  case class Var(x: String) extends Expr

  /* Declarations */
  case class ConstDecl(x: String, ed: Expr, eb: Expr) extends Expr

  /* Unary and Binary Operators */
  case class UnOp(op: Uop, e1: Expr) extends Expr

  case class BinOp(op: Bop, e1: Expr, e2: Expr) extends Expr

  /* Control constructs */
  case class If(e1: Expr, e2: Expr, e3: Expr) extends Expr

  /* I/O */
  case class Print(e1: Expr) extends Expr

  /* Functions */
  case class Function(p: Option[String], x: String, t: Typ, tann: Option[Typ], e: Expr) extends Val

  /* Function Calls */
  case class Call(e1: Expr, e2: Expr) extends Expr

  /* The above code is essentially equivalent to the following enum definitions given in the
   *  homework description, but behaves better with Scala's type inference.

  enum Expr extends Positional:
    // pretty print as AST
    override def toString: String = print.prettyAST(this)

    // Pretty print as JavaScript expression
    def prettyJS: String = print.prettyJS(this)

    // Pretty print expression as value
    def prettyVal: String = print.prettyVal(this)

    // Literals and values
    case Num(n: Double)
    case Bool(b: Boolean)
    case Str(s: String)
    case Undefined

    // Variables
    case Var(x: String)

    // Constant declarations
    case ConstDecl(x: String, ed: Expr, eb: Expr)

    // Unary and binary operator expressions
    case UnOp(op: Uop, e1: Expr)
    case BinOp(op: Bop, e1: Expr, e2: Expr)

    /* Control constructs */
    case If(e1: Expr, e2: Expr, e3: Expr)

    /* I/O */
    case Print(e1: Expr)

    /* Functions */
    case Function(p: Option[String], x: Expr, t: Option[Typ], e: Expr)

    /* Function calls */
    case Call(e0: Expr, es: Expr)

  // Values
  type Val = Expr.Num | Expr.Bool | Expr.Str | Expr.Undefined.type | Expr.Function
  */

  // Unary operators
  enum Uop:
    case UMinus, Not // - !

  // Binary operators
  enum Bop:
    case Plus, Minus, Times, Div // + - * /
    case Eq, Ne, Lt, Le, Gt, Ge // === !== < <= > >=
    case And, Or // && ||
    case Seq // ,

  /* Define values. */
  def isValue(e: Expr): Boolean = e match
    case _: Val => true
    case _ => false

  /* Define statements (used for pretty printing). */
  def isStmt(e: Expr): Boolean =
    import Bop._
    e match
      case Undefined | ConstDecl(_, _, _) |
           Print(_) => true
      case BinOp(Seq, _, e2) => isStmt(e2)
      case _ => false

  /* Get the free variables of e. */
  def fv(e: Expr): Set[String] =
    e match
      case Var(x) => Set(x)
      case ConstDecl(x, ed, eb) => fv(ed) | (fv(eb) - x)
      case Num(_) | Bool(_) | Undefined | Str(_) => Set.empty
      case UnOp(_, e1) => fv(e1)
      case BinOp(_, e1, e2) => fv(e1) | fv(e2)
      case If(e1, e2, e3) => fv(e1) | fv(e2) | fv(e3)
      case Print(e1) => fv(e1)
      case Call(e0, e1) => fv(e0) | fv(e1)
      case Function(p, x, _, _, e) => fv(e) -- p - x

  /* Check whether the given expression is closed. */
  def closed(e: Expr): Boolean = fv(e).isEmpty

  /* Pretty-print values. */
  def pretty(v: Val): String = v.toString

  /*
   * Static Type Error exception.  Throw this exception to signal a static
   * type error.
   * 
   *   throw StaticTypeError(tbad, e)
   * 
   */
  case class StaticTypeError(tbad: Typ, e: Expr) extends 
    JsException("Type Error: unexpected type: " + tbad.pretty, e.pos)

  /*
  * Stuck Type Error exception.  Throw this exception to signal getting
  * stuck in evaluation.  This exception should not get raised if
  * evaluating a well-typed expression.
  * 
  *   throw StuckError(e)
  * 
  */
  case class StuckError(e: Expr) extends JsException("stuck while evaluating expression", e.pos)

end ast
