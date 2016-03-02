package leo
package modules.seqpproc

import leo.modules.seqpproc.controlStructures._

/**
  * Facade object for various control methods of the seq. proof procedure.
  *
  * @see [[leo.modules.seqpproc.SeqPProc]]
  * @author Alexander Steen <a.steen@fu-berlin.de>
  */
object Control {
  // Generating inferences
  @inline final def paramodSet(cl: ClauseWrapper, withSet: Set[ClauseWrapper]): Set[ClauseWrapper] = inferenceControl.ParamodControl.paramodSet(cl,withSet)
  @inline final def factor(cl: ClauseWrapper): Set[ClauseWrapper] = inferenceControl.FactorizationControl.factor(cl)
  @inline final def boolext(cl: ClauseWrapper): Set[ClauseWrapper] = inferenceControl.BoolExtControl.boolext(cl)
  @inline final def primsubst(cl: ClauseWrapper): Set[ClauseWrapper] = inferenceControl.PrimSubstControl.primSubst(cl)
  // Redundancy inferences
  @inline final def indexedForwardSubsumptionTest(cl: ClauseWrapper, processed: Set[ClauseWrapper]): Boolean = ???
  // Indexing
  final def fvIndexInit(initClauses: Set[ClauseWrapper]): Unit = indexingControl.FVIndexControl.init(initClauses)
  final def fvIndexInsert(cl: ClauseWrapper): Unit = indexingControl.FVIndexControl.insert(cl)
}

/** Package collcetion control objects for inference rules.
  *
  * @see [[leo.modules.calculus.CalculusRule]] */
package inferenceControl {
  import leo.datastructures.{Clause, Literal, Term, Position}
  import Literal.Side

  package object inferenceControl {
    type LiteralIndex = Int
    type WithConfiguration = (LiteralIndex, Literal, Side)
  }

  /**
    * Object that offers methods that filter/control how paramodulation steps between a claues
    * and a set of clauses (or between two individual clauses) will be executed.
    *
    * @author Alexander Steen <a.steen@fu-berlin.de>
    * @since 22.02.16
    */
  protected[modules] object ParamodControl {
    final def paramodSet(cl: ClauseWrapper, withset: Set[ClauseWrapper]): Set[ClauseWrapper] = {
      var results: Set[ClauseWrapper] = Set()
      val withsetIt = withset.iterator

      while (withsetIt.hasNext) {
        val other = withsetIt.next()
        Out.debug(s"Paramod on ${cl.id} and ${other.id}")

        results = results ++ allParamods(cl, other)
      }

      results
    }

    final def allParamods(cl: ClauseWrapper, other: ClauseWrapper): Set[ClauseWrapper] = {
      // Do paramod with cl into other
      val res = allParamods0(cl, other)
      if (cl.id != other.id) {
        // do paramod with other into cl
        res ++ allParamods0(other, cl)
      } else res
    }

    final private def allParamods0(withWrapper: ClauseWrapper, intoWrapper: ClauseWrapper): Set[ClauseWrapper] = {
      import leo.modules.seqpproc.controlStructures.InferredFrom

      var results: Set[ClauseWrapper] = Set()

      val withClause = withWrapper.cl
      val intoClause = intoWrapper.cl

      val withConfigurationIt = new LiteralSideIterator(withClause, true, true, false)
      while (withConfigurationIt.hasNext) {
        val (withIndex, withLit, withSide) = withConfigurationIt.next()
        val withTerm = if (withSide) withLit.left else withLit.right

        assert(withClause.lits(withIndex) == withLit, s"${withIndex} in ${withClause.pretty}\n lit = ${withLit.pretty}")
        assert(withClause.lits(withIndex).polarity)

        val intoConfigurationIt = intoConfigurationIterator(intoClause)
        while (intoConfigurationIt.hasNext) {
          val (intoIndex, intoLit, intoSide, intoPos, intoTerm) = intoConfigurationIt.next()

          if (!intoTerm.isVariable && leo.modules.calculus.mayUnify(withTerm, intoTerm)) {
            Out.trace(s"May unify: ${withTerm.pretty} with ${intoTerm.pretty} (subterm at ${intoPos.pretty})")
            val newCl = OrderedParamod(withClause, withIndex, withSide,
              intoClause, intoIndex, intoSide, intoPos, intoTerm)

            val newClWrapper = ClauseWrapper(newCl, InferredFrom(OrderedParamod, Set(withWrapper, intoWrapper)))
            Out.finest(s"Result: ${newClWrapper.pretty}")
            results = results + newClWrapper
          }

        }
      }

      results
    }

    ////////////////////////////////////////////////////////
    // Utility for Paramod control
    ///////////////////////////////////////////////////////

    type Subterm = Term
    type IntoConfiguration = (inferenceControl.LiteralIndex, Literal, Side, Position, Subterm)

    final private def intoConfigurationIterator(cl: Clause): Iterator[IntoConfiguration] = new Iterator[IntoConfiguration] {

      import Literal.{leftSide, rightSide, selectSide}

      val maxLits = cl.maxLits
      var litIndex = 0
      var lits = cl.lits
      var side = leftSide
      var curSubterms: Set[Term] = null
      var curPositions: Set[Position] = null

      def hasNext: Boolean = if (lits.isEmpty) false
      else {
        val hd = lits.head
        if (!maxLits.contains(hd)) {
          lits = lits.tail
          litIndex += 1
          hasNext
        } else {
          if (curSubterms == null) {
            curSubterms = selectSide(hd, side).feasibleOccurences.keySet
            curPositions = selectSide(hd, side).feasibleOccurences(curSubterms.head)
            true
          } else {
            if (curPositions.isEmpty) {
              curSubterms = curSubterms.tail
              if (curSubterms.isEmpty) {
                if (hd.oriented || side == rightSide) {
                  lits = lits.tail
                  litIndex += 1
                  side = leftSide
                } else {
                  side = rightSide
                }
                curSubterms = null
                curPositions = null
                hasNext
              } else {
                curPositions = selectSide(hd, side).feasibleOccurences(curSubterms.head)
                assert(hasNext)
                true
              }
            } else {
              true
            }
          }
        }

      }

      def next(): IntoConfiguration = {
        if (hasNext) {
          val res = (litIndex, lits.head, side, curPositions.head, curSubterms.head)
          curPositions = curPositions.tail
          res
        } else {
          throw new NoSuchElementException
        }
      }
    }
  }

  protected[modules] object FactorizationControl {

    import leo.datastructures.Not

    final def factor(cl: ClauseWrapper): Set[ClauseWrapper] = {
      Out.debug(s"Factor in ${cl.id}")
      var res: Set[ClauseWrapper] = Set()
      val clause = cl.cl
      val maxLitIt = new LiteralSideIterator(clause, true, true, true)

      while (maxLitIt.hasNext) {
        val (maxLitIndex, maxLit, maxLitSide) = maxLitIt.next()
        val otherLitIt = new LiteralSideIterator(clause, false, true, true)

        while (otherLitIt.hasNext) {
          val (otherLitIndex, otherLit, otherLitSide) = otherLitIt.next()

          if (maxLitIndex != otherLitIndex) {
            val realMaxLit = if (maxLit.polarity)
              maxLit
            else {
              assert(maxLit.flexHead)
              Literal(Not(maxLit.left), true) // Is that right?
            }
            val realOtherLit = if (otherLit.polarity)
              otherLit
            else {
              assert(otherLit.flexHead)
              Literal(Not(otherLit.left), true)
            }
            val (maxLitMaxSide, maxLitOtherSide) = Literal.getSidesOrdered(realMaxLit, maxLitSide)
            val (otherLitMaxSide, otherLitOtherSide) = Literal.getSidesOrdered(realOtherLit, otherLitSide)
            val test1 = leo.modules.calculus.mayUnify(maxLitMaxSide, otherLitMaxSide)
            val test2 = leo.modules.calculus.mayUnify(maxLitOtherSide, otherLitOtherSide)
            Out.finest(s"Test unify ($test1): ${maxLitMaxSide.pretty} = ${otherLitMaxSide.pretty}")
            Out.finest(s"Test unify ($test2): ${maxLitOtherSide.pretty} = ${otherLitOtherSide.pretty}")
            if (test1 && test2) {
              val factor = OrderedEqFac(clause, maxLitIndex, maxLitSide, otherLitIndex, otherLitSide)
              val result = ClauseWrapper(factor, InferredFrom(OrderedEqFac, Set(cl)))
              res = res + result
            }
          }
        }
      }

      Out.trace(s"Factor result:\n\t${res.map(_.pretty).mkString("\n\t")}")
      res
    }
  }


  protected[modules] object BoolExtControl {
    final def boolext(cw: ClauseWrapper): Set[ClauseWrapper] = {
      var res: Set[ClauseWrapper] = Set()
      if (!Configuration.isSet("nbe")) {
        if (!leo.datastructures.isPropSet(ClauseWrapper.PropBoolExt, cw.propertyFlag)) {
          val (cA_boolExt, bE, bE_other) = BoolExt.canApply(cw.cl)
          if (cA_boolExt) {
            Out.debug(s"Bool Ext on: ${cw.pretty}")
            val boolExt_cws = BoolExt.apply(bE, bE_other).map(ClauseWrapper(_, InferredFrom(BoolExt, Set(cw))))
            Out.trace(s"Bool Ext result:\n\t${boolExt_cws.map(_.pretty).mkString("\n\t")}")

            res = boolExt_cws.flatMap(cw => {
              Out.finest(s"#\ncnf of ${cw.pretty}:\n\t");
              CNF(leo.modules.calculus.freshVarGen(cw.cl), cw.cl)
            }.map(c => {
              Out.finest(s"${c.pretty}\n\t");
              ClauseWrapper(c, InferredFrom(CNF, Set(cw)))
            }))
          }
        }
      }
      res
    }
  }


  protected[modules] object PrimSubstControl {
    import leo.modules.output.ToTPTP

    final def primSubst(cw: ClauseWrapper): Set[ClauseWrapper] = {
      // TODO: Read from configuration thorougness of prim subst.
      val (cA_ps, ps_vars) = StdPrimSubst.canApply(cw.cl)
      if (cA_ps) {
        Out.debug(s"Prim subst on: ${cw.id}")
        val new_ps_pre = StdPrimSubst(cw.cl, ps_vars)
        val new_ps = new_ps_pre.map{case (cl,subst) => ClauseWrapper(cl, InferredFrom(StdPrimSubst, Set((cw,ToTPTP(subst)))))}
        Out.trace(s"Prim subst result:\n\t${new_ps.map(_.pretty).mkString("\n\t")}")
        return new_ps
      }
      Set()
    }
  }


  ////////////////////////////////////////////////////////
  // Utility for inferenceControl
  ///////////////////////////////////////////////////////

  /**
    * Creates an iterator over the clause `cl` which iterates over the maximal sides (or both sides if not orientable)
    * of each literal inside `cl`.
    *
    * @param cl The clause which literals are iterated.
    * @param onlyMax If `onlyMax` is true, only maximal literals are considered.
    * @param onlyPositive If `onlyPositive` is true, only positive literals are considered..
    * @param alsoFlexheads If `alsoFlexHeads` is true, not only positive literals but also literals with a flexible head
    *                      are considered during iteration. `alsoFlexHeads` has no effect if `onlyPositive` is `false`.
    */
  protected final class LiteralSideIterator(cl: Clause, onlyMax: Boolean, onlyPositive: Boolean, alsoFlexheads: Boolean) extends Iterator[inferenceControl.WithConfiguration] {
    import Literal.{leftSide, rightSide}

    val maxLits = cl.maxLits
    var litIndex = 0
    var lits = cl.lits
    var side = leftSide

    def hasNext: Boolean = {
      if (lits.isEmpty) false
      else {
        val hd = lits.head
        if ((!onlyPositive || hd.polarity || (alsoFlexheads && hd.flexHead)) &&
          (!onlyMax || maxLits.contains(hd))) true
        else {
          litIndex = litIndex + 1
          lits = lits.tail
          hasNext
        }
      }
    }

    def next(): inferenceControl.WithConfiguration = {
      if (hasNext) {
        assert(!onlyPositive || lits.head.polarity || (alsoFlexheads && lits.head.flexHead))
        assert(!onlyMax || maxLits.contains(lits.head))
        val res = (litIndex, lits.head, side)
        if (lits.head.oriented || side == rightSide) { // Flexheads are always oriented since they are not equational
          litIndex += 1
          lits = lits.tail
          side = leftSide
        } else {
          side = rightSide
        }
        res
      } else {
        throw new NoSuchElementException
      }
    }
  }

}

package redundancyControl {
  object Subsumption {
    def testForwardSubsumption(cl: ClauseWrapper, withSet: Set[ClauseWrapper]): Boolean = ???
  }
}

package indexingControl {

  import leo.datastructures.impl.Signature

  object FVIndexControl {
    import leo.modules.indexing.CFF
    import leo.modules.indexing.FVIndex
    import leo.datastructures.Clause

    val maxFeatures: Int = 150
    var initialized = false
    var features: Seq[CFF] = Seq()

    final def init(initClauses: Set[ClauseWrapper]): Unit = {
      assert(!initialized)

      val symbs = Signature.get.allUserConstants.toVector
      val featureFunctions: Seq[CFF] = Vector(FVIndex.posLitsFeature(_), FVIndex.negLitsFeature(_)) ++
        symbs.flatMap {case symb => Seq(FVIndex.posLitsSymbolCountFeature(symb,_:Clause),
        FVIndex.posLitsSymbolDepthFeature(symb,_:Clause), FVIndex.negLitsSymbolCountFeature(symb,_:Clause), FVIndex.negLitsSymbolDepthFeature(symb,_:Clause))}

      var initFeatures: Seq[Set[Int]] = Seq()
      val featureFunctionIt = featureFunctions.iterator
      var i = 0
      while (featureFunctionIt.hasNext) {
        val cff = featureFunctionIt.next()
        val res = initClauses.map {case cw => {Out.finest(s"$i feature of ${cw.pretty} = ${cff(cw.cl)}");cff(cw.cl)}}
        initFeatures = res +: initFeatures
        i = i+1
      }
      Out.trace(s"init Features: ${initFeatures.toString()}")
      val sortedFeatures = initFeatures.zipWithIndex.sortBy(_._1.size).take(maxFeatures)
      Out.trace(s"sorted Features: ${sortedFeatures.toString()}")
      this.features = sortedFeatures.map {case (feat, idx) => featureFunctions(idx)}
      initialized = true

      val initIt = initClauses.iterator
      while (initIt.hasNext) {
        val initCl = initIt.next()
        insert(initCl)
      }
    }

    final def insert(cl: ClauseWrapper): Unit = {
      assert(initialized)
      val featureVector = features.map(_(cl.cl))
      FVIndex.add(cl.cl, featureVector)
    }
  }
}

////////////////////////////////////////////////////////
// Utility structures
///////////////////////////////////////////////////////

/**
  * Package containing utility structures wrapping clauses etc. with additional
  * information to guide proof search etc.
  *
  * @author Alexander Steen <a.steen@fu-berlin.de>
  * @since 27.02.16 (Contents older)
  */
package controlStructures {

  import leo.datastructures.{Role_Plain, Role, Clause, Pretty}
  import leo.modules.output.Output

  protected[seqpproc] abstract sealed class WrapperAnnotation extends Pretty

  case class InferredFrom(rule: leo.modules.calculus.CalculusRule, cws: Set[(ClauseWrapper, Output)]) extends WrapperAnnotation {
    def pretty: String = s"inference(${rule.name},[${rule.inferenceStatus.fold("")("status(" + _.pretty.toLowerCase + ")")}],[${
      cws.map { case (cw, add) => if (add == null) {
        cw.id
      } else {
        cw.id + ":[" + add.output + "]"
      }
      }.mkString(",")
    }])"
  }

  case object NoAnnotation extends WrapperAnnotation {
    val pretty: String = ""
  }

  case class FromFile(fileName: String, formulaName: String) extends WrapperAnnotation {
    def pretty = s"file('$fileName',$formulaName)"
  }

  object InferredFrom {
    def apply(rule: leo.modules.calculus.CalculusRule, cws: Set[ClauseWrapper]): WrapperAnnotation = {
      new InferredFrom(rule, cws.map((_, null)))
    }
  }

  protected[seqpproc] case class ClauseWrapper(id: String, cl: Clause, role: Role, annotation: WrapperAnnotation, var propertyFlag: ClauseWrapper.WrapperProp) extends Ordered[ClauseWrapper] with Pretty {
    override def equals(o: Any): Boolean = o match {
      case cw: ClauseWrapper => cw.cl == cl && cw.role == role
      case _ => false
    }

    override def hashCode(): Int = cl.hashCode() ^ role.hashCode()

    def compare(that: ClauseWrapper) = Configuration.CLAUSE_ORDERING.compare(this.cl, that.cl) // FIXME mustmatch withequals and hash

    //  def pretty: String = s"[$id]:\t${cl.pretty}\t(${annotation match {case InferredFrom(_,cws) => cws.map(_._1.id).mkString(","); case _ => ""}})"
    def pretty: String = s"[$id]:\t${cl.pretty}\t(${annotation.pretty})"
  }

  protected[seqpproc] object ClauseWrapper {
    private var counter: Int = 0

    def apply(cl: Clause, r: Role, annotation: WrapperAnnotation, propFlag: WrapperProp): ClauseWrapper = {
      counter += 1
      ClauseWrapper(s"gen_formula_$counter", cl, r, annotation, PropNoProp)
    }

    def apply(cl: Clause, annotation: WrapperAnnotation, propFlag: WrapperProp = PropNoProp): ClauseWrapper = apply(cl, Role_Plain, annotation, propFlag)

    type WrapperProp = Int
    final val PropNoProp: WrapperProp = 0
    final val PropUnified: WrapperProp = 1
    final val PropBoolExt: WrapperProp = 2
  }
}
