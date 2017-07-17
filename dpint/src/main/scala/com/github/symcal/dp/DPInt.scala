package com.github.symcal.dp

import DPInt._

import spire.syntax.cfor._

object DPInt {

  type WordT = Int

  final val word_bits = 32

  final val int_bits = 32

  final val long_bits = 64

  final val lower_uint_mask: Long = (2 << int_bits) - 1

  final val upper_uint_mask: Long = lower_uint_mask << int_bits

  def lower_uint(x: Long): Int = (x & lower_uint_mask).toInt

  def upper_uint(x: Long): Int = (x >>> int_bits).toInt

  def to_ulong(x: Int): Long = x.toLong & lower_uint_mask

  @inline def unsigned_less_than(x: Int, y: Int): Boolean = (y < 0 && x >= 0) || (x < y && (x >= 0 || y < 0))

  @inline def unsigned_less_than(x: Long, y: Long): Boolean = (y < 0 && x >= 0) || (x < y && (x >= 0 || y < 0))

  /** Algorithm 1.1. Integer addition.
    *
    * This algorithm assumes that both mantissas are equally long (have equally many words).
    *
    * @param src1     First integer.
    * @param src2     Second integer, must be exactly as long as the first one.
    * @param dst      Third integer, will be used as mutable destination.
    * @param carry_in Carry-in value.
    * @return Carry-out value.
    */
  private def add_equally_long(src1: DPInt, src2: DPInt, dst: DPInt, carry_in: Boolean): Boolean = {
    var carry_out: Boolean = carry_in
    var sum1 = 0
    var sum2 = 0
    cfor(0)(_ < src1.words, _ + 1) { i =>
      sum1 = src1.mantissa(i) + (if (carry_out) 1 else 0)
      sum2 = sum1 + src2.mantissa(i)
      dst.mantissa(i) = sum2
      // Carry occurred in sum1 if sum1 == 0; otherwise, it occurred in sum2 if sum2 < sum1 as unsigned.
      carry_out = (carry_out && sum1 == 0) || unsigned_less_than(sum2, sum1)
    }
    carry_out
  }

  private def subtract_equally_long(src1: DPInt, src2: DPInt, dst: DPInt, borrow_in: Boolean): Boolean = {
    var borrow_out: Boolean = borrow_in
    var sum1 = 0
    var sum2 = 0
    var old_mantissa1 = 0
    cfor(0)(_ < src1.words, _ + 1) { i =>
      old_mantissa1 = src1.mantissa(i)
      sum1 = old_mantissa1 - (if (borrow_out) 1 else 0)
      sum2 = sum1 - src2.mantissa(i)
      dst.mantissa(i) = sum2
      // Borrow occurred in sum1 if src1.mantissa(i) == 0; otherwise, it occurred in sum2 if sum2 > sum1 as unsigned
      borrow_out = (borrow_out && old_mantissa1 == 0) || unsigned_less_than(sum1, sum2)
    }
    borrow_out
  }
}

class DPInt(private var is_negative: Boolean = false, private var mantissa: Array[WordT] = Array(0)) extends Number {

  /** Used length of the `mantissa` array.
    * Can be smaller than the length of that array.
    */
  private var words: Int = mantissa.length

  def this(x: Int) {
    this(x < 0, Array[Int](math.abs(x)))
  }

  def this(x: Long) {
    this(x < 0, Array[Int](lower_uint(math.abs(x)), upper_uint(math.abs(x))))
  }

  @inline private def put_sign(x: Int): Int = if (is_negative) -x else x

  @inline private def put_sign(x: Long): Long = if (is_negative) -x else x

  /** Implementation of [[Number]]. */
  override def intValue(): Int = put_sign(mantissa(0))

  override def floatValue(): Float = intValue().toFloat

  override def doubleValue(): Double = longValue().toDouble

  override def longValue(): Long = put_sign(mantissa(0) + ((mantissa(1) << word_bits) & upper_uint_mask))

  // gmp-like interface
  def realloc(new_bits: Long): Unit = {
    val new_limbs = (new_bits / word_bits).toInt
    if (new_limbs > words) {
      val new_mantissa = new Array[Int](new_limbs)
      System.arraycopy(mantissa, 0, new_mantissa, 0, words)
    }
    words = new_limbs
  }

  def set_si(x: Long): Unit = {
    is_negative = x < 0
    val abs_x = math.abs(x)
    if (abs_x <= lower_uint_mask) {
      realloc(int_bits)
      mantissa(0) = lower_uint(abs_x)
    } else {
      realloc(long_bits)
      mantissa(0) = lower_uint(abs_x)
      mantissa(1) = upper_uint(abs_x)
    }
  }

}
