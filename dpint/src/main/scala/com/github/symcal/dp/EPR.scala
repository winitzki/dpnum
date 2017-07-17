package com.github.symcal.dp

/** Extended-precision real numbers of the form `d * 2^e` where d is Double with abs value <= 1 and e is Int (could be positive or negative).
  *
  */
final case class EPR(var d: Double, var e: Int = 1) extends Number {
  override def longValue(): Long = ???

  override def intValue(): Int = ???

  override def floatValue(): Float = ???

  override def doubleValue(): Double = ???

  def +(x: EPR): EPR = ???

  def -(x: EPR): EPR = ???

  def neg: EPR = copy(d = -d)

  def reciprocal: EPR = copy(e = -e)

  def *(x: EPR): EPR = ???

  def *(x: Double): EPR = copy(d = d * x)

  def /(x: Double): EPR = copy(d = d / x)

  def /(x: EPR): EPR = ???

  def pow(x: EPR): EPR = EPR.pow(this, x)

  private def adjust(): Unit = {
    if (d == 0 || d.isInfinite || d.isNaN) {
      e = 0
    } else {
      val d_norm = math.log(1.0 / d) / math.log(2)
      val new_e = e.toLong + d_norm.toLong
      // Can we represent `new_e` as Int?
      if (new_e.toInt != new_e) {
        // Exponent overflow.
        if (new_e > 0) {
          d = if (d > 0) Double.PositiveInfinity else Double.NegativeInfinity
          e = 0
        } else {
          // Exponent underflow.
          d = Double.NaN
          e = 0
        }
      } else {
        d = d / math.pow(2, d_norm)
        e = new_e.toInt
      }
    }
  }

  adjust()
}

object EPR {
  val mantissa_bits = 52

  def sqrt(x: EPR): EPR = EPR(math.sqrt(x.d * (math.abs(x.e & 1) + 1)), x.e >> 1)

  def pow(x: EPR, y: EPR): EPR = ???

}