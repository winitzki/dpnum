package com.github.symcal.dp

import java.lang.reflect.Field
import java.math.BigInteger

import com.github.symcal.dp.DPZ._
import spire.syntax.cfor.cfor

import scala.annotation.tailrec

/** Dynamic-precision integer.
  * Underlying implementation uses `Array[Int]`.
  */
class DPZ {
  private[dp] var is_negative: Boolean = false
  /** Array of unsigned digits, starting from little-endian, representing the absolute value of the integer.
    * Java's signed integers are interpreted as unsigned `mod 2^32`.
    * */
  private[dp] var mantissa: Coll = new Array(0)

  private[dp] var used_length: Int = 0

  override def toString: String = stringForm()

  def nonZero: Boolean = !isZero

  def isZero: Boolean = used_length <= 1 && mantissa(0) == 0

  def stringForm(base: Char = 10): String = {
    val capacity: Int = 2 + (used_length * math.log(DPZ.base_bits) / math.log(base)).toInt
    val res = new java.lang.StringBuilder(capacity)

    val divided = DPZ(this).abs()
    do {
      val digit = div_mod(divided, base, divided)
      res.append(digit_to_char(digit))
    } while (divided.nonZero)
    res.reverse
    if (is_negative) res.insert(0, "-")
    res.toString
  }

  def abs(): DPZ = {
    is_negative = false
    this
  }

  def negate(): DPZ = {
    is_negative = !is_negative
    this
  }

  def set(x: DPZ): DPZ = DPZ.set(this, x)

  def set(x: Int): DPZ = DPZ.set(this, x)

  def set(s: String, b: Char = 10): DPZ = DPZ.set(this, s, b)
}

object DPZ {

  type Coll = Array[Int]

  val base_bits = 32

  def set(dpz: DPZ, x: Int): DPZ = {
    dpz.used_length = 1
    dpz.is_negative = x < 0
    dpz.mantissa(0) = math.abs(x)
    dpz
  }

  def set(x: DPZ, dst: DPZ): DPZ = {
    dst.is_negative = x.is_negative
    dst.used_length = x.used_length
    dst.mantissa = x.mantissa.clone()
    dst
  }

  def apply(x: Int): DPZ = set(new DPZ, x)

  def apply(x: DPZ): DPZ = set(new DPZ, x)

  private def get_BigInteger_internals: (Field, Field) = {
    try {
      val signum = classOf[BigInteger].getField("signum")
      signum.setAccessible(true)
      val mag = classOf[BigInteger].getField("mag")
      mag.setAccessible(true)
      (signum, mag)
    } catch {
      case e: Exception ⇒
        println("failed to access internals of BigInteger:")
        e.printStackTrace()
        (null, null)
    }
  }

  private def arr_reverse(arr: Coll): Unit = {
    val len = arr.length
    cfor(0)(_ < (len >> 1), _ + 1) { i ⇒
      val t = arr(i)
      arr(i) = arr(len - 1 - i)
      arr(len - 1 - i) = t
    }
  }

  def from_BigInteger(x: BigInteger): DPZ = {
    val (signum, mag) = get_BigInteger_internals
    val res = new DPZ
    res.is_negative = signum.get(x).asInstanceOf[Int] < 0
    val mantissa = mag.get(x).asInstanceOf[Array[Int]]
    res.used_length = mantissa.length
    res.mantissa = mantissa.clone()
    arr_reverse(res.mantissa)
    res
  }

  def set(dpz: DPZ, s: String, b: Char = 10): DPZ = {
    if (s(0) == '-')
      set(dpz, get_dpz(DPZ(0), s, 1, b)).negate()
    else
      set(dpz, get_dpz(DPZ(0), s, 0, b))
  }

  @tailrec
  private def get_dpz(acc: DPZ, s: String, offset: Int, b: Char): DPZ = {
    val c = s(offset) - '0'
    val digit = if (c < 10) c else s(offset) - 'A'
    add(acc, digit, acc)
    if (s.length > offset + 1) {
      mul(acc, b, acc)
      get_dpz(acc, s, offset + 1, b)
    } else {
      acc
    }
  }

  def digit_to_char(digit: Int): Char = (if (digit < 10) digit + '0' else digit + 'A').toChar

  def add(src: DPZ, x: Int, dst: DPZ): DPZ = ???

  def sub(src: DPZ, x: Int, dst: DPZ): DPZ = ???

  def add(src1: DPZ, src2: DPZ, dst: DPZ): DPZ = ???

  def sub(src: DPZ, src2: DPZ, dst: DPZ): DPZ = ???

  def div_mod(src: DPZ, x: Int, dst: DPZ): Int = ???

  /** Low-level Char addition for positive DP numbers. Reads from the source array, adds a Char number, writes result to the destination array, returns carry bit.
    *
    * @param src        Source array.
    * @param dst        Destination array; could be the same as the source array.
    * @param offset_src Initial offset in the source array.
    * @param offset_dst Initial offset in the destination array.
    * @param count      Number of elements to be used in the source array and to be written to the destination array.
    * @param x          Number added to the source array.
    * @return Carry bit (0 or 1).
    */
  private[dp] def add_low_level(src: Coll, offset_src: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  /** Low-level Char subtraction for positive DP numbers. Reads from the source array, subtracts a Char number, writes result to the destination array, returns borrow bit.
    * Note: If borrow is nonzero, the entire array may need to be negated.
    *
    * @param src        Source array.
    * @param dst        Destination array; could be the same as the source array.
    * @param offset_src Initial offset in the source array.
    * @param offset_dst Initial offset in the destination array.
    * @param count      Number of elements to be used in the source array and to be written to the destination array.
    * @param x          Number added to the source array.
    * @return Borrow bit (0 or 1).
    */
  private[dp] def sub_low_level(src: Coll, offset_src: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  private[dp] def neg_low_level(src: Coll, offset_src: Int, count: Int): Unit = ???

  private[dp] def add_low_level(src1: Coll, offset_src1: Int, src2: Coll, offset_src2: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  private[dp] def sub_low_level(src1: Coll, offset_src1: Int, src2: Coll, offset_src2: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  private[dp] def mul_low_level(src: Coll, offset_src: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  private[dp] def div_mod_low_level(src: Coll, offset_src: Int, dst: Coll, offset_dst: Int, count: Int, x: Int): Int = ???

  def mul(src: DPZ, x: Int, dst: DPZ): Unit = {
    ???
  }

  def mul(src1: DPZ, src2: DPZ, dst: DPZ): Unit = {
    ???
  }

  def div_mod(src1: DPZ, src2: DPZ, dst: DPZ): DPZ = {
    ???
  }

  def square(src: DPZ, dst: DPZ): Unit = {
    ???
  }

  def positive_int_pow(x: Int, p: Int): DPZ = positive_int_pow(DPZ(1), DPZ(x), x, p)

  @tailrec
  def positive_int_pow(acc: DPZ, base: DPZ, x: Int, p: Int): DPZ = {
    if (p > 1) {
      if ((p & 1) != 0) {
        mul(acc, base, acc)
      }
      square(base, base)
      positive_int_pow(acc, base, x, p >> 1)
    } else if (p == 1) {
      mul(acc, x, acc)
      acc
    } else // Zero or negative power specified - return.
      acc
  }

  private def less_than(src: Coll, src_offset: Int, dst: Coll, dst_offset: Int, count: Int): Boolean = ???

  private def mantissa_is_equal_until(src: DPZ, dst: DPZ): Int = {
    var i = 0
    val len = math.min(src.used_length, dst.used_length)
    while(i < len && src.mantissa(i) == dst.mantissa(i)) {
      i += 1
    }
    i
  }

  def equal_to(src: DPZ, dst: DPZ): Boolean = {
    src.used_length == dst.used_length && (src.is_negative && dst.is_negative || !src.is_negative && !dst.is_negative) && mantissa_is_equal_until(src, dst) == src.used_length
  }

  private def abs_value_is_less(src: DPZ, dst: DPZ): Boolean = {
    dst.used_length > src.used_length || dst.used_length == src.used_length && {
      val index = mantissa_is_equal_until(src, dst)
      src.mantissa(index) < dst.mantissa(index)
    }
  }

  def less_than(src: DPZ, dst: DPZ): Boolean = {
    if (dst.is_negative) {
      src.is_negative && abs_value_is_less(dst, src)
    } else {
      src.is_negative || abs_value_is_less(src, dst)
    }
  }
}
