package leo.modules.procedures

import leo.datastructures.{Int0, Rat, Real, Term, Type, prettyRat, prettyReal}
import leo.datastructures.Term.local._
import Simplification.{normalizeRat, normalizeReal}
import leo.modules.HOLSignature.{HOLDifference, HOLGreater, HOLGreaterEq, HOLLess, HOLLessEq, HOLProduct, HOLQuotient, HOLSum, HOLUnaryMinus, LitFalse, LitTrue}
import leo.modules.SZSException
import leo.modules.output.SZS_InputError

import scala.annotation.switch
import scala.math.BigInt

object GroundArithmeticEval {

  final def apply(term: Term): Term = {
    import leo.datastructures.Term.{:::>, TypeLambda, Symbol, ∙, Rational, Real, Integer}

    @inline def applyTermOrType(arg: Either[Term, Type]): Either[Term, Type] = arg match {
      case Left(arg0) => Left(apply(arg0))
      case Right(arg0) => Right(arg0)
    }

    term match {
      case ty :::> body => mkTermAbs(ty, apply(body))
      case TypeLambda(body) => mkTypeAbs(apply(body))
      case f ∙ args if f.isConstant && args.length <= 3  => /* Count the explicit type argument */
        (f: @unchecked) match {
          case Symbol(id) =>
            (id: @switch) match {
              case HOLLess.key =>
                val (left, right) = HOLLess.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => booleanToTerm(evalLessInt(n1, n2))
                  case (Rational(n1), Rational(n2)) => booleanToTerm(evalLessRat(n1, n2))
                  case (Real(n1), Real(n2)) => booleanToTerm(evalLessReal(n1, n2))
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLLessEq.key =>
                val (left, right) = HOLLessEq.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => booleanToTerm(evalLessInt(n1, n2) || n1 == n2)
                  case (Rational(n1), Rational(n2)) => booleanToTerm(evalLessRat(n1, n2)  || (normalizeRat _ tupled n1) == (normalizeRat _ tupled n2))
                  case (Real(n1), Real(n2)) => booleanToTerm(evalLessReal(n1, n2)  || equalReal(n1,n2))
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLGreater.key =>
                val (left, right) = HOLGreater.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => booleanToTerm(evalGreaterInt(n1, n2))
                  case (Rational(n1), Rational(n2)) => booleanToTerm(evalGreaterRat(n1, n2))
                  case (Real(n1), Real(n2)) => booleanToTerm(evalGreaterReal(n1, n2))
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLGreaterEq.key =>
                val (left, right) = HOLGreaterEq.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => booleanToTerm(evalGreaterInt(n1, n2) || n1 == n2)
                  case (Rational(n1), Rational(n2)) => booleanToTerm(evalGreaterRat(n1, n2)  || (normalizeRat _ tupled n1) == (normalizeRat _ tupled n2))
                  case (Real(n1), Real(n2)) => booleanToTerm(evalGreaterReal(n1, n2)  || equalReal(n1,n2))
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLSum.key =>
                val (left, right) = HOLSum.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => mkInteger(sumInt(n1, n2))
                  case (Rational(n1), Rational(n2)) => mkRational _ tupled sumRat(n1, n2)
                  case (Real(n1), Real(n2)) => mkReal _ tupled sumReal(n1, n2)
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLDifference.key =>
                val (left, right) = HOLDifference.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => mkInteger(diffInt(n1, n2))
                  case (Rational(n1), Rational(n2)) => mkRational _ tupled diffRat(n1, n2)
                  case (Real(n1), Real(n2)) => mkReal _ tupled diffReal(n1, n2)
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLProduct.key =>
                val (left, right) = HOLProduct.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => mkInteger(prodInt(n1, n2))
                  case (Rational(n1), Rational(n2)) => mkRational _ tupled prodRat(n1, n2)
                  case (Real(n1), Real(n2)) => mkReal _ tupled prodReal(n1, n2)
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLQuotient.key =>
                val (left, right) = HOLQuotient.unapply(term).get
                val simpLeft = apply(left)
                val simpRight = apply(right)
                (simpLeft, simpRight) match {
                  case (Integer(n1), Integer(n2)) => mkRational _ tupled quotInt(n1, n2)
                  case (Rational(n1), Rational(n2)) => mkRational _ tupled quotRat(n1, n2)
                  case (Real(n1), Real(n2)) => mkReal _ tupled quotReal(n1, n2)
                  case _ => mkTermApp(mkTypeApp(f, simpLeft.ty), Seq(simpLeft, simpRight))
                }
              case HOLUnaryMinus.key =>
                val body = HOLUnaryMinus.unapply(term).get
                val simpBody = apply(body)
                simpBody match {
                  case Integer(n) => mkInteger(-n)
                  case Rational(n) => mkRational _ tupled normalizeRat(-n._1, n._2)
                  case Real(n) => mkReal _ tupled (-n._1, n._2, n._3)
                  case _ => mkTermApp(mkTypeApp(f, simpBody.ty), Seq(simpBody))
                }
              case _ => mkApp(f, args.map(applyTermOrType))
            }
        }
      case f ∙ args =>
        // f is a variable or a constant because `term` is in beta nf.
        mkApp(f, args.map(applyTermOrType))
      case _ => term
    }
  }
  // type for handeling strings of reals
  type RealString = (String, String, Int)
  // functions for normalizing reals
  // normalize so that the whole part is not just big zero and the decimal part does not begin with zeros
  final def normalizeRealString(n: RealString): Real = {
    var (wholePart, decimalPlaces, exponent) = n
    if (wholePart.isEmpty) {
      wholePart = "0"
    }
    if (decimalPlaces.isEmpty) {
      decimalPlaces = "0"
    }
    // count leading zeros of decimal places
    var leadingZerosLength = decimalPlaces.takeWhile(_ == '0').length
    decimalPlaces = decimalPlaces.reverse.dropWhile(_=='0').reverse
    // whole part bigger than zero -> check decimal places
    if (BigInt(wholePart) == bigZero) {
      if (leadingZerosLength == decimalPlaces.length) {
        // everything is zero (is this possible?) but just to be safe
        return (bigZero, bigZero, bigZero)
      } else {
        // change to new exponent
        val newN = normalizeRealToGivenExponent(n, exponent-(leadingZerosLength+1))
        wholePart = newN._1
        decimalPlaces = newN._2
        exponent = newN._3
        leadingZerosLength = decimalPlaces.takeWhile(_ == '0').length
      }
    }
    // whole part not zero and decimal part zero
    if (leadingZerosLength == decimalPlaces.length) {
      (BigInt(wholePart), bigZero, BigInt(exponent))
    } else if (leadingZerosLength == 0) {
      // no leading zeros, everything's fine
      (BigInt(wholePart), BigInt(decimalPlaces), BigInt(exponent))
    } else {
      // eliminate zeros and push the decimal places to the whole part, adjust the exponent
      val nNew = normalizeRealToGivenExponent(n, exponent - (leadingZerosLength + 1))
      (BigInt(nNew._1),BigInt(nNew._2), BigInt(nNew._3))
    }
  }
  // takes a real number and a difference and makes the exponent bigger of the amount of the difference
  // assumes, that the new exponent is smaller than the old one
  final def normalizeRealToGivenExponent(n: RealString, newExponent: Int): RealString = {
    val (wholePart, decimalPlaces, exponent) = n
    val expDifference = exponent - newExponent
    // create string to get the specific amount of characters
    val decimalLength = decimalPlaces.length
    if (decimalLength >= expDifference) {
      val firstDigits = decimalPlaces.dropRight(decimalLength-expDifference)
      val remainingDigits = decimalPlaces.takeRight(decimalLength-expDifference)
      val newWhole = wholePart+firstDigits
      val newWholeWithoutLeadingZeros = newWhole.dropWhile(_ == '0') match {
        case "" => "0"
        case result => result
      }
      if (remainingDigits.isEmpty) {
        (newWholeWithoutLeadingZeros, "0", newExponent)
      } else {
        val newDecimal = remainingDigits
        (newWholeWithoutLeadingZeros, newDecimal, newExponent)
      }
    } else {
      val additionalZeros = "0" * (expDifference - decimalLength)
      val newWhole = wholePart+decimalPlaces+additionalZeros
      val newWholeWithoutLeadingZeros = newWhole.dropWhile(_ == '0') match {
        case "" => "0"
        case result => result
      }
      (newWholeWithoutLeadingZeros, "0", newExponent)
    }
  }
  // normalize to reals to the same exponent, it will work with zeros, because they are all strings
  final def normalizeRealsToSameExponent(n1: Real, n2: Real): (RealString, RealString) = {
    val n1String = (n1._1.toString, n1._2.toString, n1._3.toInt)
    val n2String = (n2._1.toString, n2._2.toString, n2._3.toInt)
    val exponent1 = n1String._3
    val exponent2 = n2String._3
    //if they have the same exponent, everything's fine
    if(exponent1 == exponent2)
      (n1String,n2String)
    else if (exponent1 < exponent2) {
      val newN2 = normalizeRealToGivenExponent(n2String,exponent1)
      (n1String,newN2)
    } else {
      val newN1 = normalizeRealToGivenExponent(n1String, exponent2)
      (newN1, n2String)
    }
  }
  // function to check whether two reals are equal
  final def equalReal(n1: Real, n2: Real): Boolean = {
    val (newN1, newN2) = normalizeRealsToSameExponent(n1,n2)
    // get the numbers
    val (wholePart1, decimalPlaces1) = (BigInt(newN1._1), newN1._2)
    val (wholePart2, decimalPlaces2) = (BigInt(newN2._1), newN2._2)
    if (wholePart1 == wholePart2) {
      // if whole part is the same check whether the decimal places are the same
      val leadingZerosLength1 = decimalPlaces1.takeWhile(_ == '0').length
      val leadingZerosLength2 = decimalPlaces2.takeWhile(_ == '0').length
      if (leadingZerosLength1 == leadingZerosLength2) {
        if (BigInt(decimalPlaces1) == BigInt(decimalPlaces2)) {
          true
        } else false
      } else false
    } else false
  }

  @inline private[this] final def booleanToTerm(b: Boolean): Term = if (b) LitTrue else LitFalse
  private[this] final def evalLessInt(n1: Int0, n2: Int0): Boolean = n1 < n2
  private[this] final def evalLessRat(n1: Rat, n2: Rat): Boolean = {
    val (num1, denom1) = n1
    val (num2, denom2) = n2
    num1*denom2 < num2*denom1
  }
  private[this] final def evalLessReal(n1: Real, n2: Real): Boolean = { // normalize reals to the same exponent
    val (newN1, newN2) = normalizeRealsToSameExponent(n1, n2)
    // get the numbers
    val (wholePart1, decimalPlaces1) = (BigInt(newN1._1), newN1._2)
    val (wholePart2, decimalPlaces2) = (BigInt(newN2._1), newN2._2)
    // check whether the whole part is smaller
    if (wholePart1 < wholePart2) true
    else if (wholePart1 == wholePart2) {
      // if whole part is the same check whether the decimal places are smaller
      val leadingZerosLength1 = decimalPlaces1.takeWhile(_ == '0').length
      val leadingZerosLength2 = decimalPlaces2.takeWhile(_ == '0').length
      //
      if (leadingZerosLength1 == leadingZerosLength2) {
        if (BigInt(decimalPlaces1) < BigInt(decimalPlaces2)) {
          true
        } else false
      } else if (leadingZerosLength1 > leadingZerosLength2) true
      else false
    } else false
  }
  private[this] final def evalGreaterInt(n1: Int0, n2: Int0): Boolean = evalLessInt(n2, n1)
  private[this] final def evalGreaterRat(n1: Rat, n2: Rat): Boolean = evalLessRat(n2, n1)
  private[this] final def evalGreaterReal(n1: Real, n2: Real): Boolean = evalLessReal(n2, n1)

  private[this] final def sumInt(n1: Int0, n2: Int0): Int0 = n1 + n2
  private[this] final def sumRat(n1: Rat, n2: Rat): Rat = {
    val (num1, denom1) = n1
    val (num2, denom2) = n2
    // a/b + c/d =  a*d/b*d + c*b / d*b
    normalizeRat(num1*denom2 + num2*denom1, denom1 * denom2)
  }
  private[this] final def sumReal(n1: Real, n2: Real): Real = {
    val (newN1, newN2) = normalizeRealsToSameExponent(n1,n2)
    var (wholePart1, decimalPlaces1, exponent1) = newN1
    var (wholePart2, decimalPlaces2, exponent2) = newN2
    val decimalLength1 = decimalPlaces1.length
    val decimalLength2 = decimalPlaces2.length
    // calculate the whole part out of the other ones
    var newWohlePart = BigInt(wholePart1) + BigInt(wholePart2)
    // calculate the decimal part and then adjust the whole part
    // check whether the numbers are negative
    val firstNegative = wholePart1.startsWith("-")
    var secondNegative = wholePart2.startsWith("-")
    // add zeros to the smaller one, so both decimals Places have the same length
    if (decimalLength1 >= decimalLength2) {
      decimalPlaces2 += "0"*(decimalLength1-decimalLength2)
    } else {
      decimalPlaces1 += "0"*(decimalLength2-decimalLength1)
    }
    // first case: both are positive
    if( (!firstNegative && !secondNegative) || (firstNegative && secondNegative)) {
      var newDecimalPlaces = (BigInt(decimalPlaces1) + BigInt(decimalPlaces2)).toString
      println(newDecimalPlaces)
      if (newDecimalPlaces.length > decimalPlaces1.length) {
        // adjust whole part
        newDecimalPlaces = newDecimalPlaces.takeRight(decimalLength1)
        if(!firstNegative) {
          newWohlePart += 1
        } else {
          newWohlePart -= 1
        }
        normalizeRealString((newWohlePart.toString, newDecimalPlaces, exponent1))
      } else {
        normalizeRealString((newWohlePart.toString, newDecimalPlaces, exponent1))
      }
    } else if (!firstNegative && secondNegative) {
      val newDecimalPlaces = BigInt(decimalPlaces1) - BigInt(decimalPlaces2)
      if (newDecimalPlaces < bigZero) {
        newWohlePart -= 1
      }
      normalizeRealString((newWohlePart.toString, newDecimalPlaces.toString.filter(_.isDigit), exponent1))
    } else {
      val newDecimalPlaces = BigInt(decimalPlaces2) - BigInt(decimalPlaces1)
      if (newDecimalPlaces < bigZero) {
        newWohlePart -= 1
      }
      normalizeRealString((newWohlePart.toString, newDecimalPlaces.toString.filter(_.isDigit), exponent1))
    }
  }

  private[this] final def diffInt(n1: Int0, n2: Int0): Int0 = sumInt(n1, -n2)
  private[this] final def diffRat(n1: Rat, n2: Rat): Rat = sumRat(n1, (-n2._1, n2._2))
  private[this] final def diffReal(n1: Real, n2: Real): Real = sumReal(n1, (-n2._1, n2._2, n2._3))

  private[this] final def prodInt(n1: Int0, n2: Int0): Int0 = n1 * n2
  private[this] final def prodRat(n1: Rat, n2: Rat): Rat = {
    val (num1, denom1) = n1
    val (num2, denom2) = n2
    // a/b * c/d =  a*c/b*d
    normalizeRat(num1*num2, denom1*denom2)
  }
  private[this] final def prodReal(n1: Real, n2: Real): Real = {
    val (newN1, newN2) = normalizeRealsToSameExponent(n1, n2)
    val (wholePart1, decimalPlaces1, exponent1) = newN1
    val (wholePart2, decimalPlaces2, exponent2) = newN2
    val decimalLength1 = decimalPlaces1.length
    val decimalLength2 = decimalPlaces2.length
    val factor1 = BigInt(wholePart1+decimalPlaces1)
    val factor2 = BigInt(wholePart2+decimalPlaces2)
    val result = (factor1 * factor2).toString
    // println(result)
    if (result.length > (decimalLength1+decimalLength2)) {
      //println(decimalLength1+decimalLength2)
      val newDecimalPlaces = result.takeRight(decimalLength1+decimalLength2)
      //println(newDecimalPlaces)
      val newWholePart = result.dropRight(decimalLength1+decimalLength2)
      //println(newWholePart)
      normalizeRealString((newWholePart,newDecimalPlaces,exponent1+exponent2))
    } else if(result.length == (decimalLength1+decimalLength2)){
      normalizeRealString(("0",result, exponent1+exponent2))
    } else {
      val newWholePart = "0"
      val additionalZeros = "0" * (decimalLength1+decimalLength2-result.length)
      val newDecimalPlaces =  additionalZeros+result
      normalizeRealString((newWholePart,newWholePart,exponent1+exponent2))
    }
  }

  private[this] final val bigZero: BigInt = BigInt(0)
  private[this] final def quotInt(n1: Int0, n2: Int0): Rat = n2 match {
    case `bigZero` => throw new SZSException(SZS_InputError, s"Division by zero in expression '$$quotient($n1, $n2)'.")
    case _ => normalizeRat(n1, n2)
  }
  private[this] final def quotRat(n1: Rat, n2: Rat): Rat = n2._1 match {
    case `bigZero` => throw new SZSException(SZS_InputError, s"Division by zero in expression '$$quotient(${prettyRat(n1)}, ${prettyRat(n2)})'.")
    case _ => prodRat(n1, (n2._2, n2._1))
  }
  private[this] final def quotReal(n1: Real, n2: Real): Real = n2._1 match {
    case `bigZero` => throw new SZSException(SZS_InputError, s"Division by zero in expression '$$quotient(${prettyReal(n1)}, ${prettyReal(n2)})'.")
    case _ => ???
  }
}
