package leo.modules.arithmetic

import leo.datastructures.Term._
import leo.datastructures._
import leo.modules.HOLSignature._
import leo.modules.prover.State

// Procedure for checking what arithmetic types and operations are present in a given set of clauses
object CheckingArithmetic {
  final def apply(clauseSet: Set[AnnotatedClause])(implicit state: State[AnnotatedClause], sigArithmetic: SignatureArithmetic): Unit = {
    implicit val sig: Signature = state.signature
    // iterate through clauses in the given set
    val clauseIt = clauseSet.iterator
    while (clauseIt.hasNext) {
      val clause = clauseIt.next()
      // check if the clause contains arithmetic operations
      val keys = Clause.symbols(clause.cl)
      if (keys.contains(HOLSum.key) || keys.contains(HOLLess.key) || keys.contains(HOLDifference.key) || keys.contains(HOLGreater.key) || keys.contains(HOLGreaterEq.key) || keys.contains(HOLLessEq.key) || keys.contains(HOLProduct.key)) {
        //println("NOT CHANGING ARITHMETIC TO NEW FUNCTION")
        checkForArithmetic(clause)
      }
    }
  }

  final def checkForArithmetic(clause: AnnotatedClause)(implicit sig: Signature, sigArithmetic: SignatureArithmetic): Unit = {
    // all literals in the given clause
    val lits: Seq[Literal] = clause.cl.lits
    val litIt = lits.iterator
    while (litIt.hasNext) {
      val lit0 = litIt.next()
      val litLeft = lit0.left
      val litRight = lit0.right
      // check for arithmetic on both sides of the literal and store the information in the arithmetic signature
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
      case Integer(n) =>
        sigArithmetic.foundInt()
      case Rational(n,m) =>
        sigArithmetic.foundRat()
      case Real(n,m,d) =>
        sigArithmetic.foundReal()
      case ty :::> body => checkForArithmetic0(body)
      case TypeLambda(body) => checkForArithmetic0(body)
      case f ∙ args if args.length <= 3 =>
        f match {
          case Symbol(id) =>
            id match {
              case HOLSum.key =>
                sigArithmetic.foundAdd()
                val (left, right) = HOLSum.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLLess.key =>
                sigArithmetic.foundOrd()
                val (left, right) = HOLLess.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLDifference.key =>
                sigArithmetic.foundAdd()
                val (left, right) = HOLDifference.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLGreater.key =>
                sigArithmetic.foundOrd()
                val (left, right) = HOLGreater.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLGreaterEq.key =>
                sigArithmetic.foundOrd()
                val (left,right) = HOLGreaterEq.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLLessEq.key  =>
                sigArithmetic.foundOrd()
                val (left, right) = HOLLessEq.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case HOLProduct.key =>
                sigArithmetic.foundMult()
                val (left, right) = HOLProduct.unapply(term).get
                checkForArithmetic0(left)
                checkForArithmetic0(right)
              case _ =>
                args.map(allArgs)
            }
          case _ =>
            args.map(allArgs)
        }
      case f ∙ args =>
        args.map(allArgs)
    }
  }
}
