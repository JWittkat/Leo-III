package leo.modules

import leo.Configuration
import leo.datastructures.{Clause, Role_Axiom, Role_Conjecture, Signature}
import leo.modules.output.{ToTFF, ToTPTP}

/**
  * Created by lex on 3/22/17.
  */
package object external {
  object TPTPProblem {
    type Flag = Int
    final val NONE: Flag = 0
    final val WITHDEF: Flag = 1
  }

  final def createTFFProblem(problem: Set[Clause])(implicit sig: Signature): String = {
    val problemIt = problem.iterator
    val leoVersion = Configuration.VERSION
    val sb: StringBuffer = new StringBuffer
    sb.append(s"%%% This file was generated by Leo-III $leoVersion")
    sb.append("\n\n")
    sb.append(s"%% Explicit typings")
    sb.append("\n")
    sb.append(ToTFF(sig))
    sb.append("\n\n")
    sb.append(s"%% User axioms")
    sb.append("\n")
    var counter: Int = 1
    while (problemIt.hasNext) {
      val cl = problemIt.next()
      sb.append(ToTFF(cl, Role_Axiom, s"ax_$counter"))
      sb.append("\n")
      counter += 1
    }
    sb.toString
  }

  final def createTHFProblem(problem: Set[Clause], flag: TPTPProblem.Flag = TPTPProblem.NONE, conjecture: Clause = null)(implicit sig: Signature): String = {
    val problemIt = problem.iterator
    val leoVersion = Configuration.VERSION
    val sb: StringBuffer = new StringBuffer
    sb.append(s"%%% This file was generated by Leo-III $leoVersion")
    sb.append("\n\n")
    sb.append(s"%% Explicit typings")
    sb.append("\n")
    sb.append(ToTPTP(sig))
    sb.append("\n\n")
    if (leo.datastructures.isPropSet(TPTPProblem.WITHDEF, flag)) {
      sb.append(s"%% Definitions")
      sb.append("\n")
//      sb.append(""); ???
      sb.append("\n\n")
    }
    sb.append(s"%% User axioms")
    sb.append("\n")
    var counter: Int = 1
    while (problemIt.hasNext) {
      val cl = problemIt.next()
      sb.append(ToTPTP.toTPTP(s"ax_$counter", cl, Role_Axiom)(sig))
      sb.append("\n")
      counter += 1
    }
    if (conjecture != null) {
      sb.append("\n\n")
      sb.append(s"%% Conjecture\n")
      sb.append(ToTPTP.toTPTP("conjecture", conjecture, Role_Conjecture)(sig))
    }
    sb.toString
  }

}
