package leo.modules.arithmetic

// class to store the information about what arithmetic types and operations are present in the problem
class SignatureArithmetic {
  private var containsInteger = false
  private var containsRational = false
  private var containsReals = false
  private var containsAddition = false
  private var containsOrdering = false
  private var containsMultiplication = false
  // functions to get the information
  def containsInt(): Boolean = {
    containsInteger
  }
  def containsRat(): Boolean = {
    containsRational
  }
  def containsReal(): Boolean = {
    containsReals
  }
  def containsAdd(): Boolean = {
    containsAddition
  }
  def containsOrd(): Boolean = {
    containsOrdering
  }
  def containsMult(): Boolean = {
    containsMultiplication
  }
  // functions to set the information
  def foundInt(): Unit = {
    containsInteger = true
  }
  def foundRat(): Unit = {
    containsRational = true
  }
  def foundReal(): Unit = {
    containsReals = true
  }
  def foundAdd(): Unit = {
    containsAddition = true
  }
  def foundOrd(): Unit = {
    containsOrdering = true
  }
  def foundMult(): Unit = {
    containsMultiplication = true
  }
}
