package popl

object hw07 extends js.util.JsApp:
  import js.ast._
  import js._
  import Uop._, Bop._, Typ._
  /*
   * CSCI-UA.0480-055: Homework 7
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your hw08 object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your solution will _not_ be graded if it does not compile!!
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * '???' as needed to get something that compiles without error.
   *
   */

  /* Type Inference */

  // A helper function to check whether a JS type has a function type in it.
  def hasFunctionTyp(t: Typ): Boolean = t match
    case TFunction(_, _) => true
    case _ => false

  def typeInfer(env: Map[String, Typ], e: Expr): Typ =
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1)
    def checkTyp(texp: Typ, e1: Expr): Typ =
      val tgot = typ(e1)
      if texp == tgot then texp else err(tgot, e1)

    e match
      // TypePrint
      case Print(e1) => typ(e1); TUndefined

      // TypeNum
      case Num(_) => TNumber

      // TypeBool
      case Bool(_) => TBool

      // TypeUndefined
      case Undefined => TUndefined

      // TypeStr
      case Str(_) => TString

      // TypeVar
      case Var(x) => env(x)

      // TypeConst
      case ConstDecl(x, e1, e2) =>
        typeInfer(env + (x -> typ(e1)), e2)

      // TypeUMinus
      case UnOp(UMinus, e1) => typ(e1) match
        case TNumber => TNumber
        case tgot => err(tgot, e1)

      // TypeNot
      case UnOp(Not, e1) => typ(e1) match
        case TBool => TBool
        case tgot => err(tgot, e1)

      case BinOp(bop, e1, e2) =>
        bop match
          // TypePlusNum, TypePlusStr
          case Plus => typ(e1) match
            case TNumber => checkTyp(TNumber, e2)
            case TString => checkTyp(TString, e2)
            case tgot => err(tgot, e1)


          // TypeArith
          case Minus | Times | Div =>
            checkTyp(TNumber, e1)
            checkTyp(TNumber, e2)

          // TypeEqual
          case Eq | Ne => typ(e1) match {
            case t1 if !hasFunctionTyp(t1) => checkTyp(t1, e2); TBool
            case tgot => err(tgot, e1)
          }



          // TypeInequal
          case Lt | Le | Gt | Ge => typ(e1) match {
            case TNumber => checkTyp(TNumber, e2)
            case TString => checkTyp(TString, e2)
            case tgot => err(tgot, e1)
          }
            TBool


          // TypeAndOr
          case And | Or => {
            checkTyp(TBool, e1)
            checkTyp(TBool, e2)
          }


          // TypeSeq
          case Seq =>
            typ(e1); typ(e2)

      // TypeIf
      case If(e1, e2, e3) =>
        checkTyp(TBool, e1)
        checkTyp(typ(e2), e3)


      // TypeFunction, TypeFunctionAnn, TypeFunctionRec
      case Function(p, x, tannx, tann, e1) =>
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(tannx, tret)
            env + (f -> tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)

        // Bind to env2 an environment that extends env1 with bindings for x
        val env2 = env1 + (x -> tannx)
        // Match on whether the return type is specified.
        tann match
          case None => TFunction(tannx, typeInfer(env2, e1))
          case Some(tret) => typeInfer(env2, e1) match {
            case tbody if tbody == tret => TFunction(tannx, tret)
            case tbody => err(tbody, e1)
          }

      // TypeCall
      case Call(e1, es) => typ(e1) match
        case TFunction(tx, tret) =>
          checkTyp(tx, es)
          tret
        case tgot => err(tgot, e1)

  /* JakartaScript Interpreter */

  def toNum(v: Val): Double = v match
    case Num(n) => n
    case _ => throw StuckError(v)

  def toBool(v: Val): Boolean = v match
    case Bool(b) => b
    case _ => throw StuckError(v)

  def toStr(v: Val): String = v match
    case Str(s) => s
    case _ => throw StuckError(v)

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Val, v2: Val): Boolean =
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match
      case (Str(s1), Str(s2)) =>
        (bop: @unchecked) match
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
      case _ =>
        val (n1, n2) = (toNum(v1), toNum(v2))
        (bop: @unchecked) match
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2

  /* 
   * Substitutions e[v/x]
   */
  def subst(e: Expr, x: String, v: Val): Expr =
    require(closed(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def substX(e: Expr): Expr = subst(e, x, v)
    /* Body */
    e match
      case Num(_) | Bool(_) | Undefined | Str(_) => e
      case Var(y) => if x == y then v else e
      case Print(e1) => Print(substX(e1))
      case UnOp(uop, e1) => UnOp(uop, substX(e1))
      case BinOp(bop, e1, e2) => BinOp(bop, substX(e1), substX(e2))
      case If(b, e1, e2) => If(substX(b), substX(e1), substX(e2))
      case Call(e0, es) =>
        Call(substX(e0), substX(es))
      case ConstDecl(y, ed, eb) =>
        ConstDecl(y, substX(ed), if x == y then eb else substX(eb))
      case Function(p, y, tanny, tann, eb) =>
        if p.contains(x) || y == x then e else Function(p, y, tanny, tann, substX(eb))


  /*
   * This code is a reference implementation of JakartaScript without
   * functions and big-step static binding semantics.
   */
  def eval(e: Expr): Val =
    require(closed(e), "eval called on non-closed expression:\n" + e.prettyJS)
    /* Some helper functions for convenience. */
    def eToNum(e: Expr): Double = toNum(eval(e))
    def eToBool(e: Expr): Boolean = toBool(eval(e))
    e match
      /* Base Cases */

      // EvalVal
      case v: Val => v

      /* Inductive Cases */

      // EvalPrint
      case Print(e) => println(eval(e).prettyVal); Undefined

      // EvalUMinus
      case UnOp(UMinus, e1) => Num(- eToNum(e1))

      // EvalNot
      case UnOp(Not, e1) => Bool(! eToBool(e1))

      // EvalPlusStr, EvalPlusNum
      case BinOp(Plus, e1, e2) => (eval(e1), eval(e2)) match
        case (Str(s1), v2) => Str(s1 + toStr(v2))
        case (v1, Str(s2)) => Str(toStr(v1) + s2)
        case (v1, v2) => Num(toNum(v1) + toNum(v2))

      // EvalArith
      case BinOp(Minus, e1, e2) => Num(eToNum(e1) - eToNum(e2))
      case BinOp(Times, e1, e2) => Num(eToNum(e1) * eToNum(e2))
      case BinOp(Div, e1, e2) => Num(eToNum(e1) / eToNum(e2))

      // EvalAndTrue, EvalAndFalse
      case BinOp(And, e1, e2) =>
        val v1 = eval(e1)
        if toBool(v1) then /* EvalAndTrue */ eval(e2) else /* EvalAndFalse */ v1

      // EvalOrTrue, EvalOrFalse
      case BinOp(Or, e1, e2) =>
        val v1 = eval(e1)
        if toBool(v1) then /* EvalOrTrue */ v1 else /*EvalOrFalse */ eval(e2)

      // EvalSeq
      case BinOp(Seq, e1, e2) => eval(e1); eval(e2)

      // EvalEqual, EvalInequalNum, EvalInequalStr
      case BinOp(bop, e1, e2) =>
        bop match
          // EvalEqual
          case Eq | Ne =>
            val v1 = eval(e1)
            val v2 = eval(e2)
            (bop: @unchecked) match
              case Eq => Bool(v1 == v2)
              case Ne => Bool(v1 != v2)
          // EvalInequalNum, EvalInequalStr
          case _ => Bool(inequalityVal(bop, eval(e1), eval(e2)))

      // EvalIfThen, EvalIfElse
      case If(e1, e2, e3) =>
        if (eToBool(e1)) /* EvalIfThen */ eval(e2)
        else /* EvalIfElse */ eval(e3)

      // EvalConstDecl
      case ConstDecl(x, ed, eb) =>
        eval(subst(eb, x, eval(ed)))

      // EvalCall, EvalCallRec
      case Call(e0, es) =>
        val v0 = eval(e0)
        v0 match
          case Function(p, x, tannx, _, eb) =>
            val ebp = p match
              case None => eb
              case Some(x0) => subst(eb, x0, v0)
            val v = ???
            // compute common substitutions for rules EvalCall and EvalCallRec
            val ebpp = subst(ebp, x, v)
            eval(ebpp)
          case _ => throw StuckError(e)

      case Var(_) => throw StuckError(e) // this should never happen

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def evaluate(s: String): Val = eval(parse.fromString(s))

  /* Interface to run your interpreter from the command line.  You can ignore the code below. */

  def processFile(file: java.io.File): Unit =
    if debug then
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")

    val expr = handle(fail()) {
      parse.fromFile(file)
    }

    if debug then
      println("Parsed expression:")
      println(expr)

    handle(fail()) {
      val t = typeInfer(Map.empty, expr)
    }

    handle(()) {
      val v = eval(expr)
      println(v.prettyVal)
    }
