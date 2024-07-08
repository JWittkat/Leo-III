package leo.modules.arithmeticWithoutRewriting
import leo.datastructures.ClauseAnnotation.{FromSystem, NoAnnotation}
import leo.datastructures.{AnnotatedClause, Clause, ClauseAnnotation, Literal, Role_Axiom, Signature, Term, Type}
import leo.datastructures.Term.local._
import leo.datastructures.Literal._
import leo.modules.HOLSignature.{===, HOLUnaryMinus, Not, i, int, rat, real, |||}
import leo.modules.calculus.freshVarGenFromBlank
import leo.modules.control.Control
import leo.modules.prover.State

object ArithmeticAxioms {
  final def apply()(implicit state: State[AnnotatedClause], sigArithmetic: SignatureArithmetic): Unit = {
    implicit val sig: Signature = state.signature
    // Set for all axioms, that should be added
    var axioms: Set[AnnotatedClause]  = Set.empty
    // check whats in there and what axioms should be added
    if(sigArithmetic.containsAdd() || sigArithmetic.containsOrd()) {
      //println("ADD AXIOMS FOR ADDITION WITHOUT REWRITING")
      if (sigArithmetic.containsInt()) {
        //println("INT")
        axioms = axioms union getAxiomsAddition(int)
      }
      if (sigArithmetic.containsRat()) {
        //println("RAT")
        axioms = axioms union getAxiomsAddition(rat)
      }
      if (sigArithmetic.containsReal()) {
        //println("REAL")
        axioms = axioms union getAxiomsAddition(real)
      }
    }
    if(sigArithmetic.containsOrd()) {
      //println("ADD AXIOMS FOR ORDERING WITHOUT REWRITING")
      if (sigArithmetic.containsInt()) {
        axioms = axioms union getAxiomsOrdering(int)
      }
      if (sigArithmetic.containsRat()) {
        axioms = axioms union getAxiomsOrdering(rat)
      }
      if (sigArithmetic.containsReal()) {
        axioms = axioms union getAxiomsOrdering(real)
      }
    }
    if(sigArithmetic.containsMult()) {
      //println("ADD AXIOMS FOR MULTIPLICATION WITHOUT REWRITING")
      if(sigArithmetic.containsInt()) {
        axioms = axioms union getAxiomsMultiplication(int)
      }
      if (sigArithmetic.containsRat()) {
        axioms = axioms union getAxiomsMultiplication(rat)
      }
      if (sigArithmetic.containsReal()) {
        axioms = axioms union getAxiomsMultiplication(real)
      }
    }
    Control.addUnprocessed(axioms)
    /*
    for (axiom <- axioms) {
      state.addProcessed(axiom)
    }*/
  }

  final def mkNumberOfType(ty: Type, number: Int): Term = {
    if (ty == int) mkInteger(number)
    else if (ty == rat) mkRational(number,1)
    else mkReal(number,0,0)
  }

  final def getAxiomsAddition(ty: Type)(implicit sig: Signature): Set[AnnotatedClause] = {
    var axioms: Set[AnnotatedClause] = Set.empty
    val vargen = freshVarGenFromBlank
    val x = vargen(ty)
    val y = vargen(ty)
    val z = vargen(ty)
    // axiom: -(-x) = x
    val innerTermLeft = mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key), x.ty),Seq(x))
    val termLeft = mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key), innerTermLeft.ty),Seq(innerTermLeft))
    val newLit = mkLit(termLeft, x, true)
    axioms += AnnotatedClause(Clause(newLit), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x + 0 = x
    val termLeft2 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$sum").key), x.ty) ,Seq(x,mkNumberOfType(ty,0)))
    val newLit2 = mkLit(termLeft2, x, true)
    axioms += AnnotatedClause(Clause(newLit2), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x + (-x) = 0
    val innerTerm3 = mkTermApp(mkTypeApp(HOLUnaryMinus, x.ty), Seq(x))
    val termLeft3 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(x, innerTerm3))
    val newLit3 = mkLit(termLeft3, mkNumberOfType(ty,0), true)
    axioms += AnnotatedClause(Clause(newLit3), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x + y = y + x
    val termLeft4 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(x,y))
    val termRight4 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), y.ty), Seq(y,x))
    val newLit4 = mkLit(termLeft4, termRight4, true)
    axioms += AnnotatedClause(Clause(newLit4), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // axiom:  x + (y + z) = (x + y) + z
    val innerTermLeft5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key),y.ty), Seq(y,z))
    val termLeft5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key),x.ty), Seq(x,innerTermLeft5))
    val innerTermRight5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key),x.ty), Seq(x,y))
    val termRight5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), z.ty), Seq(innerTermRight5, z))
    val newLit5 = mkLit(termLeft5, termRight5,true)
    axioms += AnnotatedClause(Clause(newLit5), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: -(x + y) = (-x + -y)
    val innerTermLeft6 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key),x.ty),Seq(x,y))
    val termLeft6 = mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key), innerTermLeft6.ty), Seq(innerTermLeft6))
    // wirklich x.ty im ganzen Term?
    val termRight6 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key), x.ty), Seq(x)),mkTermApp(mkTypeApp(mkAtom(HOLUnaryMinus.key),y.ty), Seq(y))))
    val newLit6 = mkLit(termLeft6,termRight6,true)
    axioms += AnnotatedClause(Clause(newLit6), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // return axioms
    axioms
  }

  final def getAxiomsOrdering(ty: Type)(implicit sig:Signature): Set[AnnotatedClause] = {
    var axioms: Set[AnnotatedClause] = Set.empty
    val vargen = freshVarGenFromBlank
    val x = vargen(ty)
    val y = vargen(ty)
    val z = vargen(ty)
    // axiom: !(x < x)
    val innerTerm1 = mkTermApp(mkTypeApp(mkAtom(sig("$less").key), x.ty), Seq(x, x))
    val term1 = mkTermApp(mkAtom(Not.key), Seq(innerTerm1))
    val newLit1 = mkLit(term1, true)
    axioms += AnnotatedClause(Clause(newLit1), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // axiom: x < y | y < x | x = y
    val innerTermLeft2 = mkTermApp(mkTypeApp(mkAtom(sig("$less").key), x.ty), Seq(x, y))
    val innerTermMiddle2 = mkTermApp(mkTypeApp(mkAtom(sig("$less").key), y.ty), Seq(y, x))
    val innerTermRight2 = ===(x, y)
    val innerTerm2 = mkTermApp(mkAtom(|||.key), Seq(innerTermLeft2, innerTermMiddle2))
    val term2 = mkTermApp(mkAtom(|||.key), Seq(innerTerm2, innerTermRight2))
    val newLit2 = mkLit(term2, true)
    axioms += AnnotatedClause(Clause(newLit2), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // axiom: !(x < y) | !(y < x+1)
    val termLeft3 = mkTermApp(mkAtom(Not.key), Seq(innerTermLeft2))
    val innerTermRight3 = mkTermApp(mkTypeApp(mkAtom(sig("$less").key), y.ty), Seq(y, mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(x, mkNumberOfType(ty,1)))))
    val termRight3 = mkTermApp(mkAtom(Not.key), Seq(innerTermRight3))
    val term3 = mkTermApp(mkAtom(|||.key), Seq(termLeft3, termRight3))
    val newLit3 = mkLit(term3, true)
    axioms += AnnotatedClause(Clause(newLit3), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // axiom: !(x < y) | !(y < z) | !(x < z)
    // left term == left term von 9
    val termMiddle4 = mkTermApp(mkAtom(Not.key), Seq(mkTermApp(mkTypeApp(mkAtom(sig("$less").key), y.ty), Seq(y, z))))
    val termRight4 = mkTermApp(mkAtom(Not.key), Seq(mkTermApp(mkTypeApp(mkAtom(sig("$less").key), x.ty), Seq(x, z))))
    val term4 = mkTermApp(mkAtom(|||.key), Seq(mkTermApp(mkAtom(|||.key), Seq(termLeft3, termMiddle4)), termRight4))
    val newLit4 = mkLit(term4, true)
    axioms += AnnotatedClause(Clause(newLit4), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // !(x < y) | x + z | y + z
    // left term == left term 9
    val termMiddle5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(x, z))
    val termRight5 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), y.ty), Seq(y, z))
    val term5 = mkTermApp(mkAtom(|||.key), Seq(mkTermApp(mkAtom(|||.key), Seq(termLeft3, termMiddle5)), termRight5))
    val newLit5 = mkLit(term5, true)
    axioms += AnnotatedClause(Clause(newLit5), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    // axiom: x < y | y < x + 1 (ONLY INTS?????)
    // first term already existing
    if (ty == int) {
      val innerTermRight6 = mkTermApp(mkTypeApp(mkAtom(sig("$sum").key), x.ty), Seq(x, mkNumberOfType(ty, 1)))
      val termRight6 = mkTermApp(mkTypeApp(mkAtom(sig("$less").key), y.ty), Seq(y, innerTermRight6))
      val term6 = mkTermApp(mkAtom(|||.key), Seq(innerTermLeft2, termRight6))
      val newLit6 = mkLit(term6, true)
      axioms += AnnotatedClause(Clause(newLit6), Role_Axiom, FromSystem("introduced_theory",Seq.empty), ClauseAnnotation.PropNoProp)
    }
    // return axioms
    axioms
  }

  final def getAxiomsMultiplication(ty: Type)(implicit sig:Signature): Set[AnnotatedClause] = {
    var axioms: Set[AnnotatedClause] = Set.empty
    val vargen = freshVarGenFromBlank
    val x = vargen(ty)
    val y = vargen(ty)
    val z = vargen(ty)
    // axiom: x * 1 = x
    val termLeft1 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,mkNumberOfType(ty,1)))
    val newLit1 = mkLit(termLeft1, x, true)
    axioms += AnnotatedClause(Clause(newLit1), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x * 0 = 0
    val termLeft2 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,mkNumberOfType(ty,0)))
    val newLit2 = mkLit(termLeft2,mkNumberOfType(ty,0), true)
    axioms += AnnotatedClause(Clause(newLit2), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x * y = y * x
    val termLeft3 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,y))
    val termRight3 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), y.ty) ,Seq(y,x))
    val newLit3 = mkLit(termLeft3,termRight3, true)
    axioms += AnnotatedClause(Clause(newLit3), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: x * (y * z) = (x * y) * z
    val innerTermLeft4 =  mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), y.ty) ,Seq(y,z))
    val termLeft4 =  mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,innerTermLeft4))
    val termRight4 =  mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(termLeft3,z))
    val newLit4 = mkLit(termLeft4, termRight4, true)
    axioms += AnnotatedClause(Clause(newLit4), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // axiom: (x * y) + (x * z) = x * (y + z)
    val innerTermLeft5 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,z))
    val termLeft5 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), termLeft3.ty) ,Seq(termLeft3, innerTermLeft5))
    val innerTermRight5 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$sum").key), y.ty) ,Seq(y,z))
    val termRight5 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,innerTermRight5))
    val newLit5 = mkLit(termLeft5, termRight5, true)
    axioms += AnnotatedClause(Clause(newLit5), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    // x = 0 | (y * x) / x = y (ONLY REALS!!!!)
    // DIVISION??????
    if (ty == real) {
      val termLeft6 = ===(x, mkNumberOfType(ty,0))
      val innerTermLeft6 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$product").key), x.ty) ,Seq(x,y))
      val innerTermRight6 = ===(x,y)
      val termRight6 = mkTermApp(mkTypeApp(mkAtom(sig.apply("$quotient").key), innerTermLeft6.ty), Seq(innerTermLeft6,innerTermRight6))
      val term6 = mkTermApp(mkAtom(|||.key), Seq(termLeft6,termRight6))
      val newLit6 = mkLit(term6,true)
      axioms += AnnotatedClause(Clause(newLit6), Role_Axiom, FromSystem("introduced_theory",Seq.empty),ClauseAnnotation.PropNoProp)
    }
    axioms
  }
}
