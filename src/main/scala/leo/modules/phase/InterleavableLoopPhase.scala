package leo.modules.phase
import leo.{Configuration, Out}
import leo.agents.{Agent, InterferingLoopAgent}
import leo.datastructures.blackboard.Blackboard
import leo.datastructures._
import leo.datastructures.blackboard.impl.FormulaDataStore
import leo.datastructures.blackboard.scheduler.Scheduler
import leo.modules.Parsing
import leo.modules.interleavingproc.{BlackboardState, StateView, UnprocessedClause}
import leo.modules.seqpproc.SeqPProc
import leo.modules.control.Control

/**
  * Created by mwisnie on 9/28/16.
  */
class InterleavableLoopPhase (interleavingLoop : InterferingLoopAgent[StateView[AnnotatedClause]], state : BlackboardState, sig : Signature, interleavingAgents : Agent*)(blackboard: Blackboard, scheduler: Scheduler) extends CompletePhase(blackboard, scheduler) {
  /**
    * Returns the name of the phase.
    *
    * @return
    */
  override def name: String = "InterleavableLoopPhase"

  /**
    * A list of all agents to be started.
    *
    * @return
    */
  override protected val agents: Seq[Agent] = interleavingLoop +: interleavingAgents

  /**
    * Executes all defined agents and waits till no work is left.
    */
  override def execute(): Boolean = {
    implicit val s = sig

    // TODO Read external Provers / Implement external Provers
    val input2 = Parsing.readProblem(Configuration.PROBLEMFILE)
    val remainingInput = SeqPProc.effectiveInput(input2, state.state)
    // Typechecking: Throws and exception if not well-typed
    SeqPProc.typeCheck(remainingInput, state.state)

    if (state.state.negConjecture != null) {
      // Expand conj, Initialize indexes
      // We expand here already since we are interested in all symbols (possibly contained within defined symbols)
      Out.debug("## Preprocess Neg.Conjecture BEGIN")
      Out.trace(s"Neg. conjecture: ${state.state.negConjecture.pretty(sig)}")
      val simpNegConj = Control.expandDefinitions(state.state.negConjecture)
      state.state.defConjSymbols(simpNegConj)
      state.state.initUnprocessed()
      Control.initIndexes(simpNegConj +: remainingInput)
      val result = SeqPProc.preprocess(state.state, simpNegConj).filterNot(cw => Clause.trivial(cw.cl))
      Out.debug(s"# Result:\n\t${
        result.map {
          _.pretty(sig)
        }.mkString("\n\t")
      }")
      Out.trace("## Preprocess Neg.Conjecture END")
      state.state.addUnprocessed(result)
      // Save initial pre-processed set as auxiliary set for ATP calls (if existent)
      if (state.state.externalProvers.nonEmpty) {
        state.state.addInitial(result)
      }
    } else {
      // Initialize indexes
      state.state.initUnprocessed()
      Control.initIndexes(remainingInput)
    }

    // Preprocessing
    Out.debug("## Preprocess BEGIN")
    val preprocessIt = remainingInput.iterator
    while (preprocessIt.hasNext) {
      val cur = preprocessIt.next()
      Out.trace(s"# Process: ${cur.pretty(sig)}")
      val processed = SeqPProc.preprocess(state.state, cur)
      Out.debug(s"# Result:\n\t${
        processed.map {
          _.pretty(sig)
        }.mkString("\n\t")
      }")
      val preprocessed = processed.filterNot(cw => Clause.trivial(cw.cl))
      state.state.addUnprocessed(preprocessed)
      if (state.state.externalProvers.nonEmpty) {
        state.state.addInitial(preprocessed)
      }
      if (preprocessIt.hasNext) Out.trace("--------------------")
    }
    Out.trace("## Preprocess END\n\n")
    assert(state.state.unprocessed.forall(cl => Clause.wellTyped(cl.cl)), s"Not well typed:\n\t${state.state.unprocessed.filterNot(cl => Clause.wellTyped(cl.cl)).map(_.pretty(sig)).mkString("\n\t")}")
    // Debug output
    if (Out.logLevelAtLeast(java.util.logging.Level.FINEST)) {
      Out.finest(s"Clauses and maximal literals of them:")
      for (c <- state.state.unprocessed) {
        Out.finest(s"Clause ${c.pretty(sig)}")
        Out.finest(s"Maximal literal(s):")
        Out.finest(s"\t${Literal.maxOf(c.cl.lits).map(_.pretty(sig)).mkString("\n\t")}")
      }
    }
    Out.finest(s"################")
    super.execute()
  }
}
