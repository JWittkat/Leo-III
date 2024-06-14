package leo.modules.arithmeticWithoutRewriting

class SignatureArithmetic {
  private var containsInteger = false
  private var containsRational = false
  private var containsReals = false
  private var containsAddition = false
  private var containsOrdering = false
  private var containsMultiplication = false
  // get values
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
  // set values
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
