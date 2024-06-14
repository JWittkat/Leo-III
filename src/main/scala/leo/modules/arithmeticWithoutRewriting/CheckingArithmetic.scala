package leo.modules.arithmeticWithoutRewriting
import leo.datastructures.{AnnotatedClause, Clause, Literal, Signature, Term, Type}
import leo.modules.HOLSignature.{===, HOLDifference, HOLGreater, HOLGreaterEq, HOLLess, HOLLessEq, HOLProduct, HOLSum, HOLUnaryMinus, int, rat, real, |||}
import leo.datastructures.Term._
import leo.datastructures.Literal._
import leo.modules.prover.State

object CheckingArithmetic {
  final def apply(clauseSet: Set[AnnotatedClause])(implicit state: State[AnnotatedClause], sigArithmetic: SignatureArithmetic): Unit = {
    implicit val sig: Signature = state.signature
    var result: Set[AnnotatedClause] = Set.empty
    val clauseIt = clauseSet.iterator
    while (clauseIt.hasNext) {
      val clause = clauseIt.next()
      // check if there is arithmetic or ordering stuff in the clause to rename
      val keys = Clause.symbols(clause.cl)
      if (keys.contains(HOLSum.key) || keys.contains(HOLLess.key) || keys.contains(HOLDifference.key) || keys.contains(HOLGreater.key) || keys.contains(HOLGreaterEq.key) || keys.contains(HOLLessEq.key) || keys.contains(HOLProduct.key)) {
        println("CHANGING ARITHMETIC TO NEW FUNCTION")
        checkForArithmetic(clause)
      }
    }
  }

  final def checkForArithmetic(clause: AnnotatedClause)(implicit sig: Signature, sigArithmetic: SignatureArithmetic): Unit = {
    // all literals in clause
    val lits: Seq[Literal] = clause.cl.lits
    val litIt = lits.iterator
    while (litIt.hasNext) {
      val lit0 = litIt.next()
      //println(vars(lit0))
      //println(symbols(lit0))
      val litLeft = lit0.left
      val litRight = lit0.right
      // rename arithmetic function on both sides of every literal
      checkForArithmetic0(litLeft)
      checkForArithmetic0(litRight)
    }
  }

  final def checkForArithmetic0 (term: Term)(implicit sig: Signature, sigArithmetic: SignatureArithmetic): Unit = {

    @inline def allArgs(arg: Either[Term, Type]): Unit = arg match {
      case Left(arg0) => checkForArithmetic0(arg0)
      case _ =>  ()
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
      case ty :::> body => checkForArithmetic0(body)
      case TypeLambda(body) => checkForArithmetic0(body)
      case f ∙ args if args.length <= 3 =>
        f match {
          case Symbol(id) =>
            id match {
              case HOLSum.key =>
                println("SUM")
                sigArithmetic.foundAdd()
                val (left, right) = HOLSum.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLLess.key =>
                sigArithmetic.foundOrd()
                println("LESS")
                val (left, right) = HOLLess.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLDifference.key =>
                sigArithmetic.foundAdd()
                println("DIFFERENCE")
                val (left, right) = HOLDifference.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLGreater.key =>
                sigArithmetic.foundOrd()
                println("GREATER")
                val (left, right) = HOLGreater.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLGreaterEq.key =>
                sigArithmetic.foundOrd()
                println("GREATER EQUAL")
                val (left,right) = HOLGreaterEq.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLLessEq.key  =>
                sigArithmetic.foundOrd()
                println("LESS EQUAL")
                val (left, right) = HOLLessEq.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLProduct.key =>
                sigArithmetic.foundMult()
                println("PRODUCT")
                val (left, right) = HOLProduct.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case _ => println(s"ID: $id NOT IDENTIFIED YET :(")
                args.map(allArgs)
            }
          case _ => println("NOT A SYMBOL")
            args.map(allArgs)
        }
      case f ∙ args =>
        args.map(allArgs)
    }
  }
}
