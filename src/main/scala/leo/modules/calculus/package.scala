package leo.modules

import leo.datastructures.impl.Signature
import leo.datastructures.{Type, Term, Clause}
import leo.modules.output.SuccessSZS

/**
 * Created by lex on 20.05.15.
 */
package object calculus {
  trait CalculusRule {
    def name: String
    def inferenceStatus: Option[SuccessSZS] = None
  }

  trait CalculusHintRule[Hint] extends CalculusRule {
    type HintType = Hint
  }

  trait UnaryCalculusRule[Res] extends (Clause => Res) with CalculusRule {
    def canApply(cl: Clause): Boolean
  }

  trait PolyadicCalculusRule[Res] extends ((Clause, Set[Clause]) => Res) with CalculusRule {
    def canApply(cl: Clause, cls: Set[Clause]): Boolean
  }

  trait UnaryCalculusHintRule[Res, Hint] extends ((Clause, Hint) => Res) with CalculusHintRule[Hint] {
    def canApply(cl: Clause): (Boolean, Hint)
  }

  trait BinaryCalculusRule[Res, Hint] extends ((Clause, Clause, Hint) => Res) with CalculusHintRule[Hint] {
    def canApply(cl1: Clause, cl2: Clause): (Boolean, Hint)
  }

  trait FreshVarGen extends Function1[Type, Term] {
    /** Returns a fresh variable wrt. the context of this generator. */
    def apply(ty: Type): Term = Term.mkBound(ty, next(ty)._1)
    /** Returns a fresh variable represented as its loose de-bruijn index
      *  wrt. the context of this generator. */
    def next(ty: Type): (Int, Type)
    /** Return all already used variables within the context of this generator.
      * @example If `f` is a FreshVarGen for clause `cl`, then
      *          `f.existingVars == cl.implicitlyBound`
      *          he list of all free variables of a clause*/
    def existingVars: Seq[(Int, Type)]
    /**
      * Returns a copy of the underlying FreshVarGen
      */
    def copy: FreshVarGen
  }

  final private def freshVarGen0(variables:  Seq[(Int, Type)], curVar: Int): FreshVarGen = new FreshVarGen {
    private var cur = curVar
    private var vars: Seq[(Int, Type)] = variables

    override final def next(ty: Type): (Int, Type) = {
      cur = cur + 1
      vars = (cur, ty) +: vars
      (cur, ty)
    }

    override final def existingVars: Seq[(Int, Type)] = vars

    override final def copy: FreshVarGen = freshVarGen0(vars, cur)
  }

  final def freshVarGen(cl: Clause): FreshVarGen = freshVarGen0(cl.implicitlyBound, cl.maxImplicitlyBound)
  final def freshVarGenFromBlank: FreshVarGen = freshVarGen0(Seq(), 0)

  // Adopted from tomer's code:
  // n is arity of variable
  // m is arity of head
  // hdSymb is head
  // y1,..,yn are new bound variable
  // x1,..,xm are new free variables
  final def partialBinding(varGen: FreshVarGen, typ: Type, hdSymb: Term) = {
    // if typ = t1 -> t2 -> ... -> tn -> t(n+1) (where t(n+1) is not a function type)
    // then yTypes is (t1,t2,t3,..., tn)
    val yTypes = typ.funParamTypes
    // y1 ... yn new bound variables
    // yi has type ti
    // yi has de-Bruijn index (n-i)+1, i.e. y1:t1 has de-Bruijn index n and so on,
    // since they are applied as  xi y1 y2 y3 ... yn for each 1 <= i <= m
    // hence to keep type/parameter order y1 binds to the outermost lambda.
    val ys = yTypes.zip(List.range(1,typ.arity+1).reverse).map(p => Term.mkBound(p._1,p._2))
    // we need as many new free variables as arguments required by hdsymb
    // i.e. if hdSymb.ty = u1 -> u2 -> ... -> um -> u(m+1) where u(n+1) is not a function type, then
    // xs = (x1, ..., xm) where xi.ty = ui
    val xs =
      if (ys.isEmpty)
        hdSymb.ty.funParamTypes.map(p => varGen(p))
      else {
        hdSymb.ty.funParamTypes.map(p =>
          // We need to lift each new free variable by ys.size since we create new lambda binders around them
          // in the last step
          Term.mkTermApp({val i = varGen.next(Type.mkFunType(yTypes,p));Term.mkBound(i._2,i._1+ys.size)}, ys))
      }
    val t = Term.mkTermApp(hdSymb,xs)

    val aterm = Term.λ(yTypes)(t)
    aterm.etaExpand
  }

  final def skTerm(goalTy: Type, fvs: Seq[(Int, Type)]): Term = {
    val skFunc = Signature.get.freshSkolemVar(Type.mkFunType(fvs.map(_._2), goalTy))
    Term.mkTermApp(Term.mkAtom(skFunc), fvs.map {case (i,t) => Term.mkBound(t,i)})
  }


  def mayUnify(s: Term, t: Term) = mayUnify0(s,t,5)

  protected def mayUnify0(s: Term, t: Term, depth: Int): Boolean = {
    if (s == t) return true
    if (s.ty != t.ty) return false
//    if (s.ty == Signature.get.o && t.ty == Signature.get.o) return true
    if (s.freeVars.isEmpty && t.freeVars.isEmpty) return false // contains to vars, cannot be unifiable TODO: Is this right?
    if (depth <= 0) return true
//    if (s.headSymbol.ty != t.headSymbol.ty) return false

    // Match case on head symbols:
    // flex-flex always works*, flex-rigid also works*, rigid-rigid only in same symbols
    // * = if same type
    import leo.datastructures.Term._
    // rigid-rigid
    (s,t) match {
      case (Symbol(id1), Symbol(id2)) => id1 == id2
      case (Bound(_,_), _) => true
      case (_, Bound(_,_)) => true
      case (_ :::> body1, _ :::> body2) => mayUnify0(body1, body2, depth)
      case (TypeLambda(s2), TypeLambda(t2)) => mayUnify0(s2, t2, depth)
      case (Bound(_,_) ∙ _, _) => true
      case (_, Bound(_,_) ∙ _) => true
      case (f1 ∙ args1, f2 ∙ args2) if f1.ty == f2.ty && args1.length == args2.length => mayUnify0(f1, f2, depth -1) && args1.zip(args2).forall{_ match {
        case (Left(t1), Left(t2)) => mayUnify0(t1, t2, depth -1)
        case (Right(ty1), Right(ty2)) => ty1 == ty2
        case _ => false
      } }
      case _ => false
    }
  }

  import leo.datastructures.{Literal, Clause, Subst}
  final def fuseLiterals(noLift: Seq[Literal], fv_noLift: Seq[(Int, Type)], lift: Seq[Literal], fv_lift: Seq[(Int, Type)]): Seq[Literal] = {
    val subst = Subst.shift(fv_noLift.headOption.map(_._1).getOrElse(0))
    (noLift ++ lift.map(_.substitute(subst)))
  }
  final def fuseLiteralsByFVCount(cl1: Seq[Literal], fv_cl1: Seq[(Int, Type)], cl2: Seq[Literal], fv_cl2: Seq[(Int, Type)]): Seq[Literal] = {
    val (lift,nolift, liftBy) = if (fv_cl1.size > fv_cl2.size) (cl2, cl1, fv_cl2.headOption.map(_._1).getOrElse(0)) else (cl1, cl2, fv_cl1.headOption.map(_._1).getOrElse(0))
    val subst = Subst.shift(liftBy)
    (nolift ++ lift.map(_.substitute(subst)))
  }

}
