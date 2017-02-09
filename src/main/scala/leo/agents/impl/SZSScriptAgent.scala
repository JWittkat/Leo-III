package leo.agents
package impl

import leo.datastructures.ClauseAnnotation.InferredFrom
import leo.datastructures.blackboard.impl.{FormulaDataStore, SZSStore}
import leo.datastructures.context.Context
import leo.datastructures._
import leo.datastructures.blackboard._
import leo.modules.HOLSignature.{LitTrue, Not, |||}
import leo.modules.calculus.CalculusRule
import leo.modules.output._
import leo.modules.output.logger.Out

object SZSScriptAgent {
  /**
   * Creates a new [[SZSScriptAgent]] to run an external prover on a given set of formulas
   * obtained through messages in the blackboard.
   *
   * @param cmd - The filepath to an executable prover. This also might be a script to run the prover.
   * @param encodeOutput - A method to translate the Clauses to a suitable representation for the external prover
   * @param reinterpreteResult - May transform the result depending on the status of the current Context (in a CounterSAT case Theorem will prover CounterSatisfiyability)
   * @return An agent to run an external prover on the specified translation.
   */
  def apply(name : String, cmd : String, encodeOutput : Set[ClauseProxy] => Seq[String], reinterpreteResult : StatusSZS => StatusSZS) : Agent = new SZSScriptAgent(name, cmd)(encodeOutput)(reinterpreteResult)

  def apply(name : String, cmd : String) : Agent = apply(name, cmd, encodeStd, x => x)

  def encodeStd(in : Set[ClauseProxy]) : Seq[String] = {
    val ins = in.map{c => AnnotatedClause(c.cl, Role_Axiom, ClauseAnnotation.NoAnnotation, c.properties)}+ AnnotatedClause(Clause(Seq(Literal(LitTrue, false))), Role_Conjecture, ClauseAnnotation.NoAnnotation, ClauseAnnotation.PropNoProp)
    ToTPTP(ins)(SignatureBlackboard.get).map(_.apply)
  }

  protected[agents] val h : scala.collection.mutable.Map[String, SZSScriptAgent] = new scala.collection.mutable.HashMap[String, SZSScriptAgent]

  /**
    * A list of all registered script agents
 *
    * @return All SZSScriptAgents registered in the Blackbaord
    */
  def allScriptAgents : Iterable[SZSScriptAgent] = h.synchronized(h.values)

  /**
    * Returns an script agent corresponding to a certain script.
    *
    * @param script - The script we search for
    * @return Some SZSScriptAgent with this command, None if no such agent exists
    */
  def scriptAgent(script : String) : Option[SZSScriptAgent] = h.synchronized(h.get(script))

  /**
    *
    * Runs all registered provers on the given clauses.
    *
    * @param clauses The clauses to run the script on.
    */
  def execute[A <: ClauseProxy](clauses : Set[A]) : Unit = {
    // TODO Too much time. In for the translation ...
    val cast : Set[ClauseProxy] = clauses.map(_.asInstanceOf[ClauseProxy])
    val msg = CallExternal(cast)                        // TODO proof obligation
    allScriptAgents foreach {a => Blackboard().send(msg, a)}
  }
}

/**
 * A Script agent to execute a external theorem prover
 * and scans the output for the SZS status and inserts it into the Blackboard.
 */
class SZSScriptAgent(name1 : String, cmd : String)(encodeOutput : Set[ClauseProxy] => Seq[String])(reinterpreteResult : StatusSZS => StatusSZS) extends ScriptAgent(cmd) {

  override def register() = {
    super.register()
    SZSScriptAgent.h.synchronized(SZSScriptAgent.h.put(cmd, this))
  }

  override def unregister() = {
    super.unregister()
    SZSScriptAgent.h.synchronized(SZSScriptAgent.h.remove(cmd))
  }

  override val name = s"SZSScriptAgent ($name1)"

  override def encode(fs : Set[ClauseProxy]) : Seq[String] = encodeOutput(fs)

  /**
   * Scans the `input` Stream for an SZS status.
   *
   * @param input - THe input stream, that will be scanned for the status
   * @param err - THe error stream. Will be ignored.
   * @param errno - The return value.
   * @return
   */
  override def handle(input: Iterator[String], err: Iterator[String], errno: Int, fs : Set[ClauseProxy]): Delta = {
    val it = input
    val b = new StringBuilder

    while(it.hasNext){
      val line = it.next()
      b.append("  Out: "+line+"\n")
      getSZS(line) match {
        case Some(status) if status == SZS_Theorem =>     // TODO Salvage other information
          Out.debug(s"[$name]: Got positive ${status.apply} from the external prover.")
          var r =  Result()
            .insert(StatusType)(reinterpreteResult(status))
            .insert(ClauseType)(AnnotatedClause(Clause(Seq()), Role_Plain, InferredFrom(ExternalRule(name1), fs), ClauseAnnotation.PropNoProp))
          return r
        case Some(status)      =>
          ()
        case None         => ()
      }
    }
    Out.debug(s"[$name]: No positive SZS status returned in\n${b.toString}")
    Result()
  }

  /**
   * Returns some SZSStatus, if the line contains one. Else none.
   *
   * @param line - The line to scan for szs status
   * @return Some(StatusSZS) if the line contains one, else none.
   */
  def getSZS(line : String) : Option[StatusSZS] = StatusSZS.answerLine(line)

  override def filter(event: Event): Iterable[Task] = event match {
    case SZSScriptMessage(f) =>
      createTask(f)
    case CallExternal(clauses) =>
      val ts = List(new ScriptTask(cmd, clauses, this))
      ts
    case _                   => List()
  }

  private def createTask(f : ClauseProxy) : Iterable[Task] = {
    val conj : ClauseProxy = AnnotatedClause(negateClause(f.cl), Role_Conjecture, f.annotation, f.properties)
    val context : Set[ClauseProxy] = FormulaDataStore.getAll{ bf => bf.id != f.id}.toSet[ClauseProxy]
    List(new ScriptTask(cmd, context + conj, this))
  }

  private def negateClause(c : Clause) : Clause = {
    val lit : Literal = Literal(orLit(c.lits),false)
    Clause.mkClause(List(lit), Derived)
  }

  // TODO: This method inverts the polarity, this is illegal, isnt it?
  private def orLit(l : Seq[Literal]) : Term = l match {
    case Seq()        => LitTrue
    case l1 +: Seq()  => ???
    case l1 +: ls   => ???
  }

  /**
    * Method called, when a task cannot be executed
    * and is removed from the task set.
    *
    * @param t
    */
  override def taskCanceled(t: Task): Unit = {}
}







/**
 * A message with f (the to be conjecture)
 *
 * @param f
 */
case class SZSScriptMessage(f: ClauseProxy) extends Message

case class CallExternal(clauses : Set[ClauseProxy]) extends Message

case class ExternalRule(prover : String) extends CalculusRule {
  override def name: String = s"external($prover)"
}