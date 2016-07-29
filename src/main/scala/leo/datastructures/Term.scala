package leo.datastructures

import leo.Configuration
import leo.datastructures.impl.{TermImpl, Signature}


import scala.language.implicitConversions


/**
 * Abstract interface for terms and operations on them that can be
 * done in the internal language.
 * Terms are generated by
 *
 * {{{s,t ::= i (bound symbol)
 *       | c (constant symbol)
 *       | λ:tau.s (term abstraction)
 *       | s t (term application)
 *       | Λs (type abstraction)
 *       | s tau (type application)}}}
 *
 * where `c` is some symbol (constant) and `tau` is a type (see `Type`).
 *
 * @author Alexander Steen
 * @since 21.05.2014
 * @note Updated 02.06.2014 Cleaned up method set, lambda terms always have types
 * @note Updated 09.06.2014 Added pattern matcher for terms, added definition expansion
 */
trait Term extends Pretty {

  // Predicates on terms
  /** Returns true iff `this` is either a constant or a variable, i.e. `isConstant || isVariable`. */
  def isAtom: Boolean
  def isConstant: Boolean
  def isVariable: Boolean
  def isTermAbs: Boolean
  def isTypeAbs: Boolean
  def isApp: Boolean

  // Locality/Indexing properties of terms
  def indexing: Indexing = if (isIndexed) INDEXED else PLAIN
  def isIndexed: Boolean = TermIndex.contains(this)
  def locality: Locality
  def isLocal: Boolean
  def isGlobal: Boolean = !isLocal

  // Handling def. expansion
  def δ_expandable: Boolean
  def partial_δ_expand(rep: Int): Term
  def full_δ_expand: Term
  def exhaustive_δ_expand_upTo(symbs: Set[Signature#Key]): Term

  def head_δ_expandable: Boolean
  def head_δ_expand: Term

  // Queries on terms
  def ty: Type
  def ground: Boolean = freeVars.isEmpty

  // TODO: REMOVE OLD FUNCTIONS SUCH AS
  def freeVars: Set[Term] // TODO: Clarify that this does ...
  def boundVars: Set[Term]
  def looseBounds: Set[Int]  // TODO ..as opposed to this
  def metaVars: Set[(Type, Int)]
  def metaIndices: Set[Int] = metaVars.map(x => x._2)
  // TODO END

  def fv: Set[(Int, Type)]
  def tyFV: Set[Int]
  def occurrences: Map[Term, Set[Position]]
  def feasibleOccurences: Map[Term, Set[Position]]
  def headSymbol: Term
  def headSymbolDepth: Int
  def scopeNumber: (Int,Int)
  def size: Int
  def order: LangOrder

  def symbols: Set[Signature#Key]
  final def symbolsOfType(ty: Type) = {
    val sig = Signature.get
    symbols.filter({i => sig(i)._ty == ty})
  }
  // Functions for FV-Indexing
  def fvi_symbolFreqOf(symbol: Signature#Key): Int
  def fvi_symbolDepthOf(symbol: Signature#Key): Int

  // Substitutions and replacements
  /** Replace every occurrence of `what` in `this` by `by`. */
  def replace(what: Term, by: Term): Term
  def replaceAt(at: Position, by: Term): Term

  /** Apply substitution `subst` to underlying term.
    * I.e. each free variable `i` (NOT meta-vars!) occurring within `this` is replaced by `subst(i)`,
    * The term is then beta normalized */
  def substitute(termSubst: Subst, typeSubst: Subst = Subst.id): Term = closure(termSubst, typeSubst).betaNormalize
//  /** Apply type substitution `tySubst` to underlying term. */
//  def tySubstitute(tySubst: Subst): Term = this.tyClosure(tySubst).betaNormalize

  /** Explicitly create a closure, i.e. a postponed (simultaneous) substitution (of types and terms) */
  def closure(termSubst: Subst, typeSubst: Subst): Term
  /** Explicitly create a term closure, i.e. a postponed substitution */
  def termClosure(subst: Subst): Term
  /** Explicitly create a term closure with underlying type substitution `tySubst`. */
  def typeClosure(subst: Subst): Term

  // Other operations
  def compareTo(that: Term): CMP_Result = Configuration.TERM_ORDERING.compare(this, that)
  /** Returns true iff the term is well-typed. */
  def typeCheck: Boolean
  /** Return the β-nf of the term */
  def betaNormalize: Term
  /** Return the eta-long-nf of the term */
  def etaExpand: Term
  /** Eta-contract term on root level if possible */
  def topEtaContract: Term

  /// Hidden definitions
  protected[datastructures] def normalize(termSubst: Subst, typeSubst: Subst): Term
}



/////////////////////////////
// Companion factory object
/////////////////////////////


/**
 * Term Factory object. Only this class is used to create new terms.
 *
 * Current default term implementation: [[TermImpl]]
 */
object Term extends TermBank {
  import impl.TermImpl

  // Factory method delegation
  def mkAtom(id: Signature#Key): Term = TermImpl.mkAtom(id)
  def mkBound(t: Type, scope: Int): Term = TermImpl.mkBound(t,scope)
  def mkMetaVar(t: Type, id: Int): Term = TermImpl.mkMetaVar(t, id)
  def mkTermApp(func: Term, arg: Term): Term = TermImpl.mkTermApp(func, arg)
  def mkTermApp(func: Term, args: Seq[Term]): Term = TermImpl.mkTermApp(func, args)
  def mkTermAbs(t: Type, body: Term): Term = TermImpl.mkTermAbs(t, body)
  def mkTypeApp(func: Term, arg: Type): Term = TermImpl.mkTypeApp(func, arg)
  def mkTypeApp(func: Term, args: Seq[Type]): Term = TermImpl.mkTypeApp(func, args)
  def mkTypeAbs(body: Term): Term = TermImpl.mkTypeAbs(body)
  def mkApp(func: Term, args: Seq[Either[Term, Type]]): Term = TermImpl.mkApp(func, args)

  // Term bank method delegation
  val local = TermImpl.local
  def insert(term: Term): Term = TermImpl.insert(term)
  def contains(term: Term): Boolean = TermImpl.contains(term)
  def reset(): Unit = TermImpl.reset()


  // Determine order-subsets of terms

  /** FOF-compatible (unsorted) first order logic subset. */
  def firstOrder(t: Term): Boolean = {
    val polyOps = Set(HOLSignature.eqKey, HOLSignature.neqKey)
    val tys = Set(Signature.get.i, Signature.get.o)

    t match {
      case Forall(ty :::> body) => ty == Signature.get.i && firstOrder(body)
      case Exists(ty :::> body) => ty == Signature.get.i && firstOrder(body)
      case Symbol(key) ∙ sp if polyOps contains key  => sp.head.right.get == Signature.get.i && sp.tail.forall(_.fold(t => t.ty == Signature.get.i && firstOrder(t),_ => false))
      case h ∙ sp  => sp.forall(_.fold(t => tys.contains(t.ty) && firstOrder(t),_ => false))
      case ty :::> body => false
      case TypeLambda(_) => false
      case Bound(ty, sc) => ty == Signature.get.i
      case Symbol(key) => tys.contains(Signature.get(key)._ty)
    }}

  /** Many sorted-first order logic subset. */
  def manySortedFirstOrder(t: Term): Boolean = {
    val polyOps = Set(HOLSignature.eqKey, HOLSignature.neqKey)

    t match {
    case Forall(ty :::> body) => ty.isBaseType && manySortedFirstOrder(body)
    case Exists(ty :::> body) => ty.isBaseType && manySortedFirstOrder(body)
    case Symbol(key) ∙ sp if polyOps contains key  => sp.head.right.get.isBaseType && sp.tail.forall(_.fold(t => t.ty.isBaseType && manySortedFirstOrder(t),_ => false))
    case h ∙ sp  => sp.forall(_.fold(t => t.ty.isBaseType && manySortedFirstOrder(t),_ => false))
    case ty :::> body => false
    case TypeLambda(_) => false
    case Bound(ty, sc) => ty.isBaseType
    case Symbol(key) => Signature.get(key)._ty.isBaseType
  }}

  // Further utility functions
  final def mkDisjunction(terms: Seq[Term]): Term = terms match {
    case Seq() => LitFalse()
    case Seq(t, ts@_*) => ts.foldLeft(t)({case (disj, t) => |||(disj, t)})
  }
  final def mkPolyUnivQuant(bindings: Seq[Type], term: Term): Term = {
    bindings.foldRight(term)((ty,t) => Forall(λ(ty)(t)))
  }

  /** Convert tuple (i,ty) to according de-Bruijn index */
  implicit def intToBoundVar(in: (Int, Type)): Term = mkBound(in._2,in._1)
  /** Convert tuple (i,j) to according de-Bruijn index (where j is a type-de-Bruijn index) */
  implicit def intsToBoundVar(in: (Int, Int)): Term = mkBound(in._2,in._1)
  /** Convert a signature key to its corresponding atomic term representation */
  implicit def keyToAtom(in: Signature#Key): Term = mkAtom(in)

  // Legacy functions type types for statistics, like to be reused sometime
  type TermBankStatistics = (Int, Int, Int, Int, Int, Int, Map[Int, Int])
  def statistics: TermBankStatistics = TermImpl.statistics


  //////////////////////////////////////////
  // Patterns for term structural matching
  //////////////////////////////////////////
  /**
   * Pattern for matching bound symbols in terms (i.e. De-Bruijn-Indices). Usage:
   * {{{
   * t match {
   *  case Bound(ty,scope) => println("Matched bound symbol of lambda-scope "
   *                                  + scope.toString + " with type "+ ty.pretty)
   *  case _               => println("something else")
   * }
   * }}}
   */
  object Bound { def unapply(t: Term): Option[(Type, Int)] = TermImpl.boundMatcher(t) }

  /**
   * Pattern for matching meta variable symbols in terms. Usage:
   * {{{
   * t match {
   *  case MetaVar(ty,id) => println("Matched meta var symbol with id "
   *                                  + id.toString + " with type "+ ty.pretty)
   *  case _               => println("something else")
   * }
   * }}}
   */
  object MetaVar { def unapply(t: Term): Option[(Type, Int)] = TermImpl.metaVariableMatcher(t) }

  /**
   * Pattern for matching constant symbols in terms (i.e. symbols in signature). Usage:
   * {{{
   * t match {
   *  case Symbol(constantKey) => println("Matched constant symbol "+ constantKey.toString)
   *  case _                   => println("something else")
   * }
   * }}}
   */
  object Symbol { def unapply(t: Term): Option[Signature#Key] = TermImpl.symbolMatcher(t) }

  /**
   * Pattern for matching a general application (i.e. terms of form `(h ∙ S)`), where
   * `h` is the function term and `S` is a sequence of terms/types (arguments).
   * Usage:
   * {{{
   * t match {
   *  case s ∙ args => println("Matched application. Head: " + s.pretty
   *                                            + " Args: " + args.map.fold(_.pretty,_.pretty)).toString
   *  case _       => println("something else")
   * }
   * }}}
   */
  object ∙ { def unapply(t: Term): Option[(Term, Seq[Either[Term, Type]])] = TermImpl.appMatcher(t) }

  /**
   * Pattern for matching a term application (i.e. terms of form `(h ∙ S)`), where
   * `h` is the function term and `S` is a sequence of terms only (arguments).
   * Usage:
   * {{{
   * t match {
   *  case s ∙ args => println("Matched application. Head: " + s.pretty
   *                                            + " Args: " + args.map.fold(_.pretty,_.pretty)).toString
   *  case _       => println("something else")
   * }
   * }}}
   */
  object TermApp {
    def unapply(t: Term): Option[(Term, Seq[Term])] = t match {
      case h ∙ sp => if (sp.forall(_.isLeft)) {
                        Some(h, sp.map(_.left.get))
                      } else {
                        None
                      }
      case _ => None
    }
  }

  /**
   * Pattern for matching a type application (i.e. terms of form `(h ∙ S)`), where
   * `h` is the function term and `S` is a sequence of types only (arguments).
   * Usage:
   * {{{
   * t match {
   *  case s ∙ args => println("Matched application. Head: " + s.pretty
   *                                            + " Args: " + args.map.fold(_.pretty,_.pretty)).toString
   *  case _       => println("something else")
   * }
   * }}}
   */
  object TypeApp {
    def unapply(t: Term): Option[(Term, Seq[Type])] = t match {
      case h ∙ sp => if (sp.forall(_.isRight)) {
        Some(h, sp.map(_.right.get))
      } else {
        None
      }
      case _ => None
    }
  }

  /**
   * Pattern for matching (term) abstractions in terms (i.e. terms of form `(\(ty)(s))` where `ty` is a type). Usage:
   * {{{
   * t match {
   *  case ty :::> s => println("Matched abstraction. Type of parameter: " + ty.pretty
   *                                                           + " Body: " + s.pretty)
   *  case _         => println("something else")
   * }
   * }}}
   */
  object :::> { def unapply(t: Term): Option[(Type,Term)] = TermImpl.termAbstrMatcher(t) }

  /**
   * Pattern for matching (type) abstractions in terms (i.e. terms of form `/\(s)`). Usage:
   * {{{
   * t match {
   *  case TypeLambda(s) => println("Matched type abstraction. Body: " + s.pretty)
   *  case _             => println("something else")
   * }
   * }}}
   */
  object TypeLambda { def unapply(t: Term): Option[Term] = TermImpl.typeAbstrMatcher(t) }
}
