package leo.modules.arithmeticWithRewriting
import leo.datastructures.{AnnotatedClause, Clause, Literal, Signature, Term, Type}
import leo.modules.HOLSignature.{===, HOLDifference, HOLGreater, HOLGreaterEq, HOLLess, HOLLessEq, HOLProduct, HOLQuotient, HOLSum, HOLUnaryMinus, int, rat, real, |||}
import leo.datastructures.Term._
import leo.datastructures.Literal._
import leo.modules.prover.State

object RewritingArithmetic {
  final def apply(clauseSet: Set[AnnotatedClause])(implicit state: State[AnnotatedClause], sigArithmetic: SignatureArithmetic): Set[AnnotatedClause] = {
    implicit val sig: Signature = state.signature
    var result: Set[AnnotatedClause] = Set.empty
    val clauseIt = clauseSet.iterator
    while (clauseIt.hasNext) {
      val clause = clauseIt.next()
      // check if there is arithmetic or ordering stuff in the clause to rename
      val keys = Clause.symbols(clause.cl)
      if (keys.contains(HOLSum.key) || keys.contains(HOLLess.key) || keys.contains(HOLDifference.key) || keys.contains(HOLGreater.key) || keys.contains(HOLGreaterEq.key) || keys.contains(HOLLessEq.key) || keys.contains(HOLProduct.key) || keys.contains(HOLQuotient.key)) {
        println("CHANGING ARITHMETIC TO NEW FUNCTION")
        result += renameArithmetic(clause)
      }
      else {
        result += clause
      }
    }
    result
  }

  final def renameArithmetic(clause: AnnotatedClause)(implicit sig: Signature, sigArithmetic: SignatureArithmetic): AnnotatedClause = {
    var newLits: Set[Literal] = Set.empty
    // all literals in clause
    val lits: Seq[Literal] = clause.cl.lits
    val litIt = lits.iterator
    while (litIt.hasNext) {
      val lit0 = litIt.next()
      println(vars(lit0))
      println(symbols(lit0))
      val litLeft = lit0.left
      val litRight = lit0.right
      // rename arithmetic function on both sides of every literal
      val leftNew = renameArithmetic0(litLeft)
      val rightNew = renameArithmetic0(litRight)
      // create new literal
      val newLit = mkLit(leftNew, rightNew, lit0.polarity)
      newLits += newLit
    }
    // create new annotated clause
    val result = AnnotatedClause(Clause(newLits),clause.role,clause.annotation,clause.properties)
    result
  }

  final def renameArithmetic0 (term: Term)(implicit sig: Signature, sigArithmetic: SignatureArithmetic): Term = {

    @inline def allArgs(arg: Either[Term, Type]): Either[Term, Type] = arg match {
      case Left(arg0) => Left(renameArithmetic0(arg0))
      case Right(arg0) => Right(arg0)
    }
    term match {
      case Bound(n,m) =>
        if (n == int) {
          sigArithmetic.foundInt()
        }
        else if (n == rat) {
          sigArithmetic.foundRat()
        }
        else if (n == real) {
          sigArithmetic.foundReal()
        }
        term
      case Symbol(n) =>
        if (n == sig("$int").key) {
          sigArithmetic.foundInt()
        }
        else if (n == sig("$rat").key) {
          sigArithmetic.foundRat()
        }
        else if (n == sig("$real").key) {
          sigArithmetic.foundReal()
        }
        term
      case Integer(n) =>
        sigArithmetic.foundInt()
        term
      case Rational(n,m) =>
        sigArithmetic.foundRat()
        term
      case Real(n,m,d) =>
        sigArithmetic.foundReal()
        term
      case ty :::> body => mkTermAbs(ty, renameArithmetic0(body))
      case TypeLambda(body) => mkTypeAbs(renameArithmetic0(body))
      case f ∙ args if args.length <= 3 =>
        f match {
          case Symbol(id) =>
            id match {
              case HOLSum.key =>
                println("RENAME SUM")
                println(sigArithmetic.containsAdd())
                sigArithmetic.foundAdd()
                println(sigArithmetic.containsAdd())
                val (left, right) = HOLSum.unapply(term).get
                println(sig.apply("$$sum").key)
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$sum").key),newLeft.ty), Seq(newLeft, newRight))
              case HOLLess.key =>
                sigArithmetic.foundOrd()
                println("RENAME LESS")
                val (left, right) = HOLLess.unapply(term).get
                println(sig.apply("$$less").key)
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$less").key),newLeft.ty), Seq(newLeft, newRight))
              case HOLDifference.key =>
                sigArithmetic.foundAdd()
                println("RENAME DIFFERENCE")
                val (left, right) = HOLDifference.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$sum").key),left.ty), Seq(newLeft, mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key),newRight.ty),Seq(newRight))))
              case HOLGreater.key =>
                sigArithmetic.foundOrd()
                println("RENAME GREATER")
                val (left, right) = HOLGreater.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$less").key), newLeft.ty), Seq(newRight,newLeft))
              case HOLGreaterEq.key =>
                sigArithmetic.foundOrd()
                println("RENAME GREATER EQUAL")
                val (left,right) = HOLGreaterEq.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkAtom(|||.key), Seq(mkTermApp(mkTypeApp(mkAtom(sig("$$less").key), newLeft.ty),Seq(newRight, newLeft)), ===(newLeft, newRight)))
              case HOLLessEq.key  =>
                sigArithmetic.foundOrd()
                println("RENAME LESS EQUAL")
                val (left, right) = HOLLessEq.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkAtom(|||.key), Seq(mkTermApp(mkTypeApp(mkAtom(sig("$$less").key), newLeft.ty),Seq(newLeft, newRight)), ===(newLeft, newRight)))
              case HOLProduct.key =>
                sigArithmetic.foundMult()
                println("RENAME PRODUCT")
                val (left, right) = HOLProduct.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$product").key), newLeft.ty), Seq(newLeft,newRight))
              case HOLQuotient.key =>
                println("RENAME QUOTIENT")
                val (left, right) = HOLQuotient.unapply(term).get
                val newLeft = renameArithmetic0(left)
                val newRight = renameArithmetic0(right)
                mkTermApp(mkTypeApp(mkAtom(sig("$$quotient").key), newLeft.ty), Seq(newLeft,newRight))
              case _ => println(s"ID: $id NOT IDENTIFIED YET :(")
                mkApp(f, args.map(allArgs))
            }
          case _ => println("NOT A SYMBOL")
            mkApp(f, args.map(allArgs))
        }
      case f ∙ args =>
        mkApp(f, args.map(allArgs))
    }
  }
}
