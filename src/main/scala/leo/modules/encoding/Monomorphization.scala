package leo.modules.encoding

import leo.datastructures.{Clause, Literal, Signature, Subst, Term, Type}
import leo.modules.calculus.{TypeUnification, TypeSubst}

import scala.annotation.tailrec

/**
  * Translates polymorphic problems into
  * monomorphic problems by heuristic type variable instantiation.
  *
  * @author Alexander Steen <a.steen@fu-berlin.de>
  * @since March 2017
  */
object Monomorphization {
  import scala.collection.mutable

  type MonoResult = (Problem, Signature)
  type Instance = Seq[Type]
  type Instances = Set[Instance]
  type InstanceInfo = mutable.Map[Signature#Key, Instances]
  type PolySymbols = InstanceInfo

  final def apply(problem: Problem)(implicit sig: Signature): (Problem, Signature) = {
    val clsIt = problem.iterator
    val newSig: Signature = Signature.freshWithHOL() // Even if problem is not formulated in HOL
    // we dont care: Since only non-fixed constants will be printed out and
    // ids are re-calculated anyway in apply0(term)
    var monoProblem: Problem = Set.empty
    var polyAxioms: Set[Clause] = Set.empty
    val instanceInfo: InstanceInfo = mutable.Map()
    while (clsIt.hasNext) {
      val cl = clsIt.next()
      if (cl.typeVars.isEmpty) monoProblem += apply0(cl, newSig, instanceInfo)(sig)
      else polyAxioms += cl
    }
    monoProblem = monoProblem union generateMonoAxioms(polyAxioms, instanceInfo, newSig)(sig)
    (monoProblem, newSig)
  }

  private final val blackListedConsts: Seq[String] = Seq("xapp")

  private final def generateMonoAxioms(polyAxioms: Set[Clause], instanceInfo: InstanceInfo, newSig: Signature)(sig: Signature): Problem = {
    println(s"Mono instances:")
    for ((id, instances) <- instanceInfo) {
      println(s"${sig(id).name}:")
      println("\t" + instances.map(_.map(_.pretty(sig)).mkString(",")).mkString("\n\t"))
    }
    println(s"Poly axioms:")
    for (ax <- polyAxioms) {
      println("\t" + ax.pretty(sig))
    }
    var monoAxioms: Set[Clause] = Set.empty
    val polyAxiomsIt = polyAxioms.iterator
//    val newInstanceInfo: InstanceInfo = mutable.Map()
    while (polyAxiomsIt.hasNext) {
      val polyAxiom = polyAxiomsIt.next()
      println(s"Poly ax: ${polyAxiom.pretty(sig)}")
      val polySymbs = polySymbols(polyAxiom, instanceInfo)
      for ((id, instances) <- polySymbs) {
        println(s"${sig(id).name}:")
        println("\t" + instances.map(_.map(_.pretty(sig)).mkString(",")).mkString("\n\t"))
      }

//      val tySubstsIt = tySubsts.iterator
//      while (tySubstsIt.hasNext) {
//        val tySubst = tySubstsIt.next()
//        val newAxiom = polyAxiom.substitute(Subst.id, tySubst)
//        if (newAxiom.typeVars.isEmpty) monoAxioms += newAxiom
//      }
    }

    monoAxioms
  }

  private final def polySymbols(polyAxiom: Clause, instanceInfo: InstanceInfo): PolySymbols = {
    val polySymbolTable: InstanceInfo = mutable.Map()
    val litsIt = polyAxiom.lits.iterator
    while(litsIt.hasNext) {
      val lit = litsIt.next()
      polySymbols(lit, instanceInfo, polySymbolTable)
    }
    polySymbolTable
  }
  private final def polySymbols(lit: Literal, instanceInfo: InstanceInfo, polySymbolTable: PolySymbols): Unit = {
    if (!lit.equational) polySymbols(lit.left, instanceInfo, polySymbolTable)
    else {
      polySymbols(lit.left, instanceInfo, polySymbolTable)
      polySymbols(lit.right, instanceInfo, polySymbolTable)
    }
  }

  private final def polySymbols(term: Term, instanceInfo: InstanceInfo, polySymbolTable: PolySymbols): Unit = {
    import leo.datastructures.Term.{∙,:::>, Symbol}
    term match {
      case f ∙ args => f match {
        case Symbol(id) if f.ty.isPolyType =>
          val (typeArgs, termArgs) = partitionArgs(args)
          if (typeArgs.exists(_.typeVars.nonEmpty)) {
            // polySymbol
            updateInstanceInfo(polySymbolTable, id, typeArgs)
          } else {
            // update instance info
            updateInstanceInfo(instanceInfo, id, typeArgs)
          }
          val termArgsIt = termArgs.iterator
          while (termArgsIt.hasNext) {
            val termArg = termArgsIt.next()
            polySymbols(termArg, instanceInfo, polySymbolTable)
          }
        case _ =>
          val (_, termArgs) = partitionArgs(args) // tyargs should be empty
          val termArgsIt = termArgs.iterator
          while (termArgsIt.hasNext) {
            val termArg = termArgsIt.next()
            polySymbols(termArg, instanceInfo, polySymbolTable)
          }
      }
      case _ :::> body => polySymbols(body, instanceInfo, polySymbolTable)
    }
  }
//  private final def mergeMaps(map1: Map[Signature#Key, Set[Seq[Type]]], map2: Map[Signature#Key, Set[Seq[Type]]]): Map[Signature#Key, Set[Seq[Type]]] = {
//    var result = map1
//    val map2It = map2.iterator
//    while (map2It.hasNext) {
//      val (id, entry) = map2It.next()
//      if (result.contains(id)) {
//        val newEntry = result(id) union entry
//        result = result + (id -> newEntry)
//      } else result = result + (id -> entry)
//    }
//    result
//  }

//  private final def instances0(t: Term, instanceInfo: InstanceInfo): Set[TypeSubst] =  {
//    import leo.datastructures.Term.{∙, Symbol, :::>}
//    import Term.local.mkTypeApp
//    t match {
//      case f ∙ args => f match {
//        case Symbol(id) =>
//          if (instanceInfo.contains(id)) {
//            val knownMonoArgs = instanceInfo(id)
//            val (typeArgs, termArgs) = partitionArgs(args)
//            val polyF = mkTypeApp(f, typeArgs)
//            knownMonoArgs.map { instance =>
//              val freshVargen = leo.modules.calculus.freshVarGenFromBlank
//              HuetsPreUnification.unify(freshVargen, polyF, instance)
//            }
//          } else {
//            val argsIt = args.iterator
//            var result: Set[TypeSubst] = Set.empty
//            while (argsIt.hasNext) {
//              val arg = argsIt.next()
//              if (arg.isLeft) {
//                val termArg = arg.left.get
//                val localResult = instances0(termArg, instanceInfo)
//                result = multiply(result, localResult)
//              }
//            }
//            result
//          }
//        case _ =>
//          val argsIt = args.iterator
//          var result: Set[TypeSubst] = Set.empty
//          while (argsIt.hasNext) {
//            val arg = argsIt.next()
//            if (arg.isLeft) {
//              val termArg = arg.left.get
//              val localResult = instances0(termArg, instanceInfo)
//              result = multiply(result, localResult)
//            }
//          }
//          result
//      }
//      case ty :::> body => instances0(body, instanceInfo)
//      case _ => ???
//    }
//  }
  private final def multiply(set1: Set[TypeSubst], set2: Set[TypeSubst]): Set[TypeSubst] = {
    var result: Set[TypeSubst] = Set.empty
    val set1It = set1.iterator
    while (set1It.hasNext) {
      val elem1 = set1It.next()
      val set2It = set2.iterator
      while(set2It.hasNext) {
        val elem2 = set2It.next()
        result = result + elem1.comp(elem2).normalize + elem2.comp(elem1).normalize
      }
    }
    result
  }

  private final def apply0(cl: Clause, newSig: Signature, instanceInfo: InstanceInfo)(sig: Signature): Clause = {
    Clause(cl.lits.map(apply0(_, newSig, instanceInfo)(sig)))
  }

  private final def apply0(lit: Literal, newSig: Signature, instanceInfo: InstanceInfo)(sig: Signature): Literal = {
    if (lit.equational) {
      val newLeft = apply0(lit.left, newSig, instanceInfo)(sig)
      val newRight = apply0(lit.right, newSig, instanceInfo)(sig)
      Literal.mkLit(newLeft, newRight, lit.polarity)
    } else {
      Literal.mkLit(apply0(lit.left, newSig, instanceInfo)(sig), lit.polarity)
    }
  }

  private final def apply0(t: Term, newSig: Signature, instanceInfo: InstanceInfo)(implicit sig: Signature): Term = {
    import Term.local._
    import Term.{Symbol, ∙, Bound, :::>}
    t match {
      case f ∙ args => f match {
        case Symbol(id) => if (f.ty.isPolyType) {
          val (tyArgs, termArgs) = partitionArgs(args)
          val monoType = f.ty.instantiate(tyArgs)
          val name = monoInstanceName(id, tyArgs)(sig)
          updateInstanceInfo(instanceInfo, id, tyArgs)
          val newF = if (newSig.exists(name)) mkAtom(newSig(name).key)(newSig)
          else mkAtom(newSig.addUninterpreted(name, convertType(monoType, sig, newSig)))(newSig)
          val newArgs = termArgs.map(arg => apply0(arg, newSig, instanceInfo))
          mkTermApp(newF, newArgs)
        } else {
          assert(args.forall(_.isLeft), s"not all arguments of ${f.pretty(sig)} (type: ${f.ty.pretty(sig)}) terms in: ${t.pretty(sig)}")
          val name = escape(sig(id).name)
          val newF = if (newSig.exists(name)) mkAtom(newSig(name).key)(newSig)
          else mkAtom(newSig.addUninterpreted(name, convertType(sig(id)._ty, sig, newSig)))(newSig)
          val newArgs = args.map(arg => apply0(arg.left.get, newSig, instanceInfo))
          mkTermApp(newF, newArgs)
        }
        case Bound(ty,idx) => // bound head cannot have poly type
          assert(args.forall(_.isLeft), s"not all arguments of ${f.pretty(sig)} (type: ${f.ty.pretty(sig)}) terms in: ${t.pretty(sig)}")
          val newF = mkBound(convertType(ty, sig, newSig), idx)
          val newArgs = args.map(arg => apply0(arg.left.get, newSig, instanceInfo))
          mkTermApp(newF, newArgs)
        case _ => throw new IllegalArgumentException
      }
      case ty :::> body =>
        val convertedType = convertType(ty, sig, newSig)
        λ(convertedType)(apply0(body, newSig, instanceInfo)(sig))
//      case Bound(ty, idx) => mkBound(convertType(ty, sig, newSig), idx)
      case _ => throw new IllegalArgumentException(s"${t.pretty(sig)} was given")
    }
  }

  final def convertType(ty: Type, oldSig: Signature, newSig: Signature): Type = {
    import Type._
    ty match {
      case BaseType(id) =>
        val name = escape(oldSig(id).name)
        if (newSig.exists(name)) mkType(newSig(name).key)
        else mkType(newSig.addBaseType(name))
      case ComposedType(id, args) =>
        val name = monoInstanceName(id, args)(oldSig)
        if (newSig.exists(name)) mkType(newSig(name).key)
        else mkType(newSig.addBaseType(name))
      case in -> out =>
        val convertedIn = convertType(in, oldSig,newSig)
        val convertedOut = convertType(out, oldSig, newSig)
        mkFunType(convertedIn, convertedOut)
      case _ => throw new IllegalArgumentException
    }
  }

  private final def partitionArgs(args: Seq[Either[Term, Type]]): (Seq[Type], Seq[Term]) = partitionArgs0(Seq(), args)
  @tailrec final def partitionArgs0(acc: Seq[Type], args: Seq[Either[Term, Type]]): (Seq[Type], Seq[Term]) = {
    if (args.isEmpty) (acc, Seq.empty)
    else {
      val hd = args.head
      if (hd.isLeft) (acc, args.map(_.left.get))
      else partitionArgs0(acc :+ hd.right.get, args.tail)
    }
  }

  private final def monoInstanceName(id: Signature#Key, tyArgs: Seq[Type])(sig: Signature): String = {
    val sb: StringBuffer = new StringBuffer
    sb.append(safeName(sig(id).name))
    sb.append("_")
    val tyArgsIt = tyArgs.iterator
    while (tyArgsIt.hasNext) {
      val tyArg = tyArgsIt.next()
      sb.append(canonicalTyName(tyArg)(sig))
      if (tyArgsIt.hasNext) sb.append("_")
    }
    sb.toString
  }
  private final def canonicalTyName(ty: Type)(sig: Signature): String = {
    import Type._
    ty match {
      case BaseType(id) => sig(id).name.replaceAll("\\$", "D")
      case ComposedType(id, args) => s"${sig(id).name}_${args.map(canonicalTyName(_)(sig)).mkString("_")}"
      case _ => throw new IllegalArgumentException // bound, poly cannot happen, -> types should at this level be encoded to fun
    }
  }

  private final def updateInstanceInfo(instanceInfo: InstanceInfo, symbol: Signature#Key, instance: Instance): Unit = {
    if (instanceInfo.contains(symbol)) {
      val entry = instanceInfo(symbol)
      instanceInfo.+=(symbol -> (entry+instance))
    } else {
      instanceInfo.+=(symbol -> Set(instance))
    }
  }
}
