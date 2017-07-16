package com.github.symcal.dpint

/** Dynamic-precision integer.
  * Underlying implementation uses `Array[Long]`.
  *
  * @param is_negative Whether the integer is negative.
  * @param mantissa Array of digits, starting from little-endian, representing the absolute value of the integer.
  */
case class DPZ(private var is_negative: Boolean = false, private var mantissa: Array[Int] = Array(0)) {

}

object DPZ {

}