package com.github.symcal.dpint

import DPInt._

object DPInt {
  def lower_uint(x: Long): Int = (x & 0xFFFFFFFF).toInt

  def upper_uint(x: Long): Int = (x >>> 32).toInt

  def to_ulong(x: Int): Long = x.toLong & 0xFFFFFFFF

}

class DPInt(private var isNegative: Boolean = false, private var mantissa: Array[Int] = Array(0)) extends Number {

  /** Used length of the `mantissa` array.
    *
    */
  private var limbs: Int = mantissa.length

  def this(x: Int) {
    this(x < 0, Array[Int](math.abs(x)))
  }

  def this(x: Long) {
    this(x < 0, Array[Int](lower_uint(math.abs(x)), upper_uint(math.abs(x))))
  }

  @inline private def bits: Long = mantissa.length * 32

  @inline private def putSign(x: Int): Int = if (isNegative) -x else x

  @inline private def putSign(x: Long): Long = if (isNegative) -x else x

  /** Implementation of [[Number]]. */
  override def intValue(): Int = putSign(mantissa(0))

  override def floatValue(): Float = intValue().toFloat

  override def doubleValue(): Double = longValue().toDouble

  override def longValue(): Long = putSign(mantissa(0) + ((mantissa(1) << 32) & 0xFFFFFFFF00000000L))

  // gmp-like interface
  def mpz_realloc(new_bits: Long): Unit = {
    val new_limbs = (new_bits / 32).toInt
    if (new_bits > bits) {
      mantissa = new Array[Int](new_limbs)
      limbs = mantissa.length
    } else {
      limbs = new_limbs
    }
  }

  def mpz_set_si(x: Long): Unit = {
    isNegative = x < 0
    mpz_realloc(64)
    mantissa(0) = lower_uint(x)
    mantissa(1) = upper_uint(x)
  }

}
