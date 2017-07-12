package com.github.symcal.dpint

/*
Copyright (c) 2015-2016 The Huldra Project.
See the LICENSE file for too long unnecessary boring license bullshit that otherwise would be written here.
Tl;dr: Use this possibly broken code however you like.

Representation:
Base is 2^32.
Magnitude as array in little endian order.
The len first ints count as the number.
Sign is represented by a sign int (-1 or 1).
Internally zero is allowed to have either sign. (Otherwise one would have to remember to check for sign-swap for div/mul etc...)
Zero has length 1 and dig[0]==0.

Principle: No Exceptions.
If a programmer divides by zero he has only himself to blame. It is OK to have undefined behavior.

Beware:
Nothing should be assumed about a position of the internal array that is not part of the number, e.g. that it is 0.
Beware of signed extensions!

Organization: Locality of reference
Stuff that has something in common should generally be close to oneanother in the code.
So stuff regarding multiplication is bunched together.

Coding style: Klein / As long as it looks good
Generally brackets on new line, but exception can be made for small special cases, then they may be aligned on the same line.
Never space after for or if or akin, it looks ugly.
Bracketless loops may be on one line. For nested bracketless loops each should be indented on a new line.
*/

import java.util._
import java.io._
import java.util.concurrent._
//import java.math.BigInteger;
/**
  * <p>A class for arbitrary-precision integer arithmetic purely written in Java.</p>
  * <p>This class does what {@link java.math.BigInteger} doesn't.<br />
  * It is <b>faster</b>, and it is <b>mutable</b>!<br />
  * It supports <b>ints</b> and <b>longs</b> as parameters!<br />
  * It has a way faster {@link #toString()} method!<br />
  * It utilizes a faster multiplication algorithm for those nasty big numbers!</p>
  *
  * <p>Get it today! Because performance matters (and we like Java).</p>
  *
  * @author Simon Klein
  * @version 0.7
  */
object BigInt {
  /**
    * Used to cast a (base 2^32) digit to a long without getting unwanted sign extension.
    **/
    private val mask = (1L << 32) - 1

  /**
    * Multiplies two magnitude arrays and returns the result.
    *
    * @param u    The first magnitude array.
    * @param ulen The length of the first array.
    * @param v    The second magnitude array.
    * @param vlen The length of the second array.
    * @return A ulen+vlen length array containing the result.
    * @complexity O(n^2)
    **/
  private def naiveMul(u: Array[Int], ulen: Int, v: Array[Int], vlen: Int) = {
    val res = new Array[Int](ulen + vlen)
    var carry = 0
    var tmp = 0L
    var ui = u(0) & mask
    var j = 0
    while ( {
      j < vlen
    }) {
      tmp = ui * (v(j) & mask) + carry
      res(j) = tmp.toInt
      carry = tmp >>> 32

        j += 1

    }
    res(vlen) = carry.toInt
    var i = 1
    while ( {
      i < ulen
    }) {
      ui = u(i) & mask
      carry = 0
      var j = 0
      while ( {
        j < vlen
      }) {
        tmp = ui * (v(j) & mask) + (res(i + j) & mask) + carry
        res(i + j) = tmp.toInt
        carry = tmp >>> 32
        {
          j += 1; j - 1
        }
      }
      res(i + vlen) = carry.toInt
      {
        i += 1; i - 1
      }
    }
    res
  }

  /**
    * Multiplies partial magnitude arrays x[off..off+n) and y[off...off+n) and returns the result.
    * Algorithm: Karatsuba
    *
    * @param x   The first magnitude array.
    * @param y   The second magnitude array.
    * @param off The offset, where the first element is residing.
    * @param n   The length of each of the two partial arrays.
    * @complexity O(n^1.585)
    **/
  private def kmul(x: Array[Int], y: Array[Int], off: Int, n: Int) = { // x = x1*B^m + x0
    // y = y1*B^m + y0
    // xy = z2*B^2m + z1*B^m + z0
    // z2 = x1*y1, z0 = x0*y0, z1 = (x1+x0)(y1+y0)-z2-z0
    if (n <= 32) { //Basecase
      val z = new Array[Int](2 * n)
      var carry = 0
      var tmp = 0L
      var xi = x(off) & mask
      var j = 0
      while ( {
        j < n
      }) {
        tmp = xi * (y(off + j) & mask) + carry
        z(j) = tmp.toInt
        carry = tmp >>> 32
        {
          j += 1; j - 1
        }
      }
      z(n) = carry.toInt
      var i = 1
      while ( {
        i < n
      }) {
        xi = x(off + i) & mask
        carry = 0
        var j = 0
        while ( {
          j < n
        }) {
          tmp = xi * (y(off + j) & mask) + (z(i + j) & mask) + carry
          z(i + j) = tmp.toInt
          carry = tmp >>> 32
          {
            j += 1; j - 1
          }
        }
        z(i + n) = carry.toInt
        {
          i += 1; i - 1
        }
      }
      return z
    }
    val b = n >>> 1
    val z2 = kmul(x, y, off + b, n - b)
    val z0 = kmul(x, y, off, b)
    val x2 = new Array[Int](n - b + 1)
    val y2 = new Array[Int](n - b + 1)
    var carry = 0
    var i = 0
    while ( {
      i < b
    }) {
      carry = (x(off + b + i) & mask) + (x(off + i) & mask) + carry
      x2(i) = carry.toInt
      carry >>>= 32
      {
        i += 1; i - 1
      }
    }
    if ((n & 1) != 0) x2(b) = x(off + b + b)
    if (carry != 0) if ( {
      x2(b) += 1; x2(b)
    } == 0) {
      x2(b + 1) += 1; x2(b + 1)
    }
    carry = 0
    var i = 0
    while ( {
      i < b
    }) {
      carry = (y(off + b + i) & mask) + (y(off + i) & mask) + carry
      y2(i) = carry.toInt
      carry >>>= 32
      {
        i += 1; i - 1
      }
    }
    if ((n & 1) != 0) y2(b) = y(off + b + b)
    if (carry != 0) if ( {
      y2(b) += 1; y2(b)
    } == 0) {
      y2(b + 1) += 1; y2(b + 1)
    }
    val z1 = kmul(x2, y2, 0, n - b + (if (x2(n - b) != 0 || y2(n - b) != 0) 1
    else 0))
    val z = new Array[Int](2 * n)
    System.arraycopy(z0, 0, z, 0, 2 * b) //Add z0
    System.arraycopy(z2, 0, z, b + b, 2 * (n - b)) //Add z2
    //Add z1
    carry = 0
    var i = 0
    while ( {
      i < 2 * b
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) - (z2(i) & mask) - (z0(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    while ( {
      i < 2 * (n - b)
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) - (z2(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    while ( {
      i < z1.length
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    if (carry != 0) while ( {
      {
        z(i + b) += 1; z(i + b)
      } == 0
    }) {
      i += 1; i
    }
    z
  }

  /**
    * Multiplies partial magnitude arrays x[off..off+n) and y[off...off+n) and returns the result.
    * Algorithm: Parallell Karatsuba
    *
    * @param x    The first magnitude array.
    * @param y    The second magnitude array.
    * @param off  The offset, where the first element is residing.
    * @param n    The length of each of the two partial arrays.
    * @param lim  The recursion depth up until which we will spawn new threads.
    * @param pool Where spawn threads will be added and executed.
    * @throws 		Various thread related exceptions.
    * @complexity O(n^1.585)
    **/
  @throws[Exception]
  private def pmul(x: Array[Int], y: Array[Int], off: Int, n: Int, lim: Int, pool: ExecutorService) = {
    val b = n >>> 1
    val left = pool.submit(new Callable[Array[Int]]() {
      @throws[Exception]
      override def call: Array[Int] = if (lim == 0) kmul(x, y, off, b)
      else pmul(x, y, off, b, lim - 1, pool)
    })
    val right = pool.submit(new Callable[Array[Int]]() {
      @throws[Exception]
      override def call: Array[Int] = if (lim == 0) kmul(x, y, off + b, n - b)
      else pmul(x, y, off + b, n - b, lim - 1, pool)
    })
    val x2 = new Array[Int](n - b + 1)
    val y2 = new Array[Int](n - b + 1)
    var carry = 0
    var i = 0
    while ( {
      i < b
    }) {
      carry = (x(off + b + i) & mask) + (x(off + i) & mask) + carry
      x2(i) = carry.toInt
      carry >>>= 32
      {
        i += 1; i - 1
      }
    }
    if ((n & 1) != 0) x2(b) = x(off + b + b)
    if (carry != 0) if ( {
      x2(b) += 1; x2(b)
    } == 0) {
      x2(b + 1) += 1; x2(b + 1)
    }
    carry = 0
    var i = 0
    while ( {
      i < b
    }) {
      carry = (y(off + b + i) & mask) + (y(off + i) & mask) + carry
      y2(i) = carry.toInt
      carry >>>= 32
      {
        i += 1; i - 1
      }
    }
    if ((n & 1) != 0) y2(b) = y(off + b + b)
    if (carry != 0) if ( {
      y2(b) += 1; y2(b)
    } == 0) {
      y2(b + 1) += 1; y2(b + 1)
    }
    val mid = pool.submit(new Callable[Array[Int]]() {
      @throws[Exception]
      override def call: Array[Int] = if (lim == 0) kmul(x2, y2, 0, n - b + (if (x2(n - b) != 0 || y2(n - b) != 0) 1
      else 0))
      else pmul(x2, y2, 0, n - b + (if (x2(n - b) != 0 || y2(n - b) != 0) 1
      else 0), lim - 1, pool)
    })
    val z = new Array[Int](2 * n)
    val z0 = left.get
    System.arraycopy(z0, 0, z, 0, 2 * b)
    val z2 = right.get
    System.arraycopy(z2, 0, z, b + b, 2 * (n - b))
    val z1 = mid.get
    carry = 0
    var i = 0
    while ( {
      i < 2 * b
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) - (z2(i) & mask) - (z0(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    while ( {
      i < 2 * (n - b)
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) - (z2(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    while ( {
      i < z1.length
    }) {
      carry = (z(i + b) & mask) + (z1(i) & mask) + carry
      z(i + b) = carry.toInt
      carry >>= 32
      {
        i += 1; i - 1
      }
    }
    if (carry != 0) while ( {
      {
        z(i + b) += 1; z(i + b)
      } == 0
    }) {
      i += 1; i
    }
    z
  }
}

class BigInt extends Number with Comparable[BigInt] {
  /**
    * The sign of this number.
    * 1 for positive numbers and -1 for negative numbers.
    * Zero can have either sign.
    */
    private var sign = 0
  /**
    * The number of digits of the number (in base 2^32).
    **/
  private var len = 0
  /**
    * The digits of the number, i.e., the magnitude array.
    */
  private var dig = null

  /**
    * Creates a BigInt from the given parameters.
    * The input-array will be used as is and not be copied.
    *
    * @param sign The sign of the number.
    * @param v    The magnitude of the number, the first position gives the least significant 32 bits.
    * @param len  The (first) number of entries of v that are considered part of the number.
    * @complexity O(1)
    */
  def this(sign: Int, v: Array[Int], len: Int) {
    this()
    assign(sign, v, len)
  }

  /**
    * Creates a BigInt from the given parameters.
    * The contents of the input-array will be copied.
    *
    * @param sign The sign of the number.
    * @param v    The magnitude of the number, the first position gives the least significant 8 bits.
    * @param len  The (first) number of entries of v that are considered part of the number.
    * @complexity O(n)
    */
  def this(sign: Int, v: Array[Byte], vlen: Int)

  /**
    * Creates a BigInt from the given parameters.
    * The input-value will be interpreted as unsigned.
    *
    * @param sign The sign of the number.
    * @param val  The magnitude of the number.
    * @complexity O(1)
    */
  def this(sign: Int, `val`: Int) {
    this()
    dig = new Array[Int](1)
    uassign(sign, `val`)
  }

  def this(sign: Int, `val`: Long) {
    this()
    dig = new Array[Int](2)
    uassign(sign, `val`)
  }

  /**
    * Creates a BigInt from the given int.
    * The input-value will be interpreted a signed value.
    *
    * @param val The value of the number.
    * @complexity O(1)
    */
  def this(`val`: Int) {
    this()
    dig = new Array[Int](1)
    assign(`val`)
  }

  /**
    * Creates a BigInt from the given long.
    * The input-value will be interpreted a signed value.
    *
    * @param val The value of the number.
    * @complexity O(1)
    */
  def this(`val`: Long) {
    this()
    dig = new Array[Int](2)
    assign(`val`)
  }

  /**
    * Creates a BigInt from the given string.
    *
    * @param s A string representing the number in decimal.
    * @complexity O(n^2)
    **/
  def this(s: String) {
    this()
    assign(s)
  }

  /**
    * Creates a BigInt from the given char-array.
    *
    * @param s A char array representing the number in decimal.
    * @complexity O(n^2)
    **/
  def this(s: Array[Char]) {
    this()
    assign(s)
  }

  /**
    * Parses a part of a char array as an unsigned decimal number.
    *
    * @param s    A char array representing the number in decimal.
    * @param from The index (inclusive) where we start parsing.
    * @param to   The index (exclusive) where we stop parsing.
    * @return The parsed number.
    * @complexity O(n)
    */
  private def parse(s: Array[Char], from: Int, to: Int) = {
    var res = s(from) - '0'
    while ( {
      {
        from += 1; from
      } < to
    }) res = res * 10 + s(from) - '0'
    res
  }

  /**
    * Multiplies this number and then adds something to it.
    * I.e. sets this = this*mul + add.
    *
    * @param mul The value we multiply our number with, mul < 2^31.
    * @param add The value we add to our number, add < 2^31.
    * @complexity O(n)
    */
  private def mulAdd(mul: Int, add: Int) = {
    var carry = 0
    var i = 0
    while ( {
      i < len
    }) {
      carry = mul * (dig(i) & BigInt.mask) + carry
      dig(i) = carry.toInt
      carry >>>= 32
      {
        i += 1; i - 1
      }
    }
    if (carry != 0) dig({
      len += 1; len - 1
    }) = carry.toInt
    carry = (dig(0) & BigInt.mask) + add
    dig(0) = carry.toInt
    if ((carry >>> 32) != 0) {
      var i = 1
      while ( {
        i < len && {
          dig(i) += 1; dig(i)
        } == 0
      }) {
        i += 1; i
      }
      if (i == len) dig({
        len += 1; len - 1
      }) = 1 //Todo: realloc() for general case?
    }
  }

  /**
    * Reallocates the magnitude array to one twice its size.
    *
    * @complexity O(n)
    */
  private def realloc() = {
    val res = new Array[Int](dig.length * 2)
    System.arraycopy(dig, 0, res, 0, len)
    dig = res
  }

  /**
    * Reallocates the magnitude array to one of the given size.
    *
    * @param newLen The new size of the magnitude array.
    * @complexity O(n)
    */
  private def realloc(newLen: Int) = {
    val res = new Array[Int](newLen)
    System.arraycopy(dig, 0, res, 0, len)
    dig = res
  }

  /**
    * Creates a copy of this number.
    *
    * @return The BigInt copy.
    * @complexity O(n)
    */
  def copy = new BigInt(sign, util.Arrays.copyOf(dig, len), len)

  /**
    * Assigns the given number to this BigInt object.
    *
    * @param The BigInt to copy/assign to this BigInt.
    * @complexity O(n)
    */
  def assign(other: BigInt): Unit = {
    sign = other.sign
    assign(other.dig, other.len)
  }

  /**
    * Assigns the content of the given magnitude array and the length to this number.
    * The contents of the input will be copied.
    *
    * @param v    The new magnitude array content.
    * @param vlen The length of the content, vlen > 0.
    * @complexity O(n)
    */
  private def assign(v: Array[Int], vlen: Int) = {
    if (vlen > dig.length) dig = new Array[Int](vlen + 2)
    System.arraycopy(v, 0, dig, 0, len = vlen)
  } //Todo: Better and more consistent naming.
  /**
    * Assigns the given BigInt parameter to this number.
    * The input magnitude array will be used as is and not copied.
    *
    * @param sign The sign of the number.
    * @param v    The magnitude of the number.
    * @param len  The length of the magnitude array to be used.
    * @complexity O(1)
    */
  def assign(sign: Int, v: Array[Int], len: Int): Unit = {
    this.sign = sign
    this.len = len
    dig = v
  }

  /**
    * Assigns the given BigInt parameter to this number.
    * Assumes no leading zeroes of the input-array, i.e. that v[vlen-1]!=0, except for the case when vlen==1.
    *
    * @param sign The sign of the number.
    * @param v    The magnitude of the number.
    * @param vlen The length of the magnitude array to be used.
    * @complexity O(n)
    */
  def assign(sign: Int, v: Array[Byte], vlen: Int): Unit = {
    len = (vlen + 3) / 4
    if (len > dig.length) dig = new Array[Int](len + 2)
    this.sign = sign
    var tmp = vlen / 4
    var j = 0
    var i = 0
    while ( {
      i < tmp
    }) {
      dig(i) = v(j + 3) << 24 | (v(j + 2) & 0xFF) << 16 | (v(j + 1) & 0xFF) << 8 | v(j) & 0xFF {
        i += 1; i - 1
      }
      j += 4
    }
    if (tmp != len) {
      tmp = v({
        j += 1; j - 1
      }) & 0xFF
      if (j < vlen) {
        tmp |= (v({
          j += 1; j - 1
        }) & 0xFF) << 8
        if (j < vlen) tmp |= (v(j) & 0xFF) << 16
      }
      dig(len - 1) = tmp
    }
  }

  /**
    * Assigns the given number to this BigInt object.
    *
    * @param s A string representing the number in decimal.
    * @complexity O(n^2)
    **/
  def assign(s: String): Unit = assign(s.toCharArray)

  /**
    * Assigns the given number to this BigInt object.
    *
    * @param s A char array representing the number in decimal.
    * @complexity O(n^2)
    **/
  def assign(s: Array[Char]): Unit = {
    sign = if (s(0) == '-') -1
    else 1
    len = s.length + (sign - 1 >> 1)
    val alloc = if (len < 10) 1
    else (len * 3402L >>> 10).toInt + 32 >>> 5 //3402 = bits per digit * 1024
    if (dig == null || alloc > dig.length) dig = new Array[Int](alloc)
    var j = len % 9
    if (j == 0) j = 9
    j -= (sign - 1 >> 1)
    dig(0) = parse(s, 0 - (sign - 1 >> 1), j)
    len = 1
    while ( {
      j < s.length
    }) mulAdd(1 _000_000_000, parse(s, j, j += 9))
  }

  /**
    * Assigns the given number to this BigInt object.
    *
    * @param s   The sign of the number.
    * @param val The magnitude of the number (will be intepreted as unsigned).
    * @complexity O(1)
    */
  def uassign(s: Int, `val`: Int): Unit = {
    sign = s
    len = 1
    dig(0) = `val`
  }

  def uassign(s: Int, `val`: Long): Unit = {
    sign = s
    len = 2
    if (dig.length < 2) realloc(2)
    dig(0) = (`val` & BigInt.mask).toInt
    dig(1) = (`val` >>> 32).toInt
    if (dig(1) == 0) {
      len -= 1; len
    }
  }

  /**
    * Assigns the given non-negative number to this BigInt object.
    *
    * @param val The number interpreted as unsigned.
    * @complexity O(1)
    */
  def uassign(`val`: Int): Unit = uassign(1, `val`)

  def uassign(`val`: Long): Unit = uassign(1, `val`)

  /**
    * Assigns the given number to this BigInt object.
    *
    * @param val The number to be assigned.
    * @complexity O(1)
    */
  def assign(`val`: Int): Unit = uassign(if (`val` < 0) -1
  else 1, if (`val` < 0) -`val`
  else `val`)

  def assign(`val`: Long): Unit = uassign(if (`val` < 0) -1
  else 1, if (`val` < 0) -`val`
  else `val`)

  /**
    * Tells whether this number is zero or not.
    *
    * @return true if this number is zero, false otherwise
    * @complexity O(1)
    */
  def isZero: Boolean = len == 1 && dig(0) == 0

  /**
    * Sets this number to zero.
    *
    * @complexity O(1)
    */
  private def setToZero() = {
    dig(0) = 0
    len = 1
    sign = 1 //Remove?
  }

  /**
    * Compares the absolute value of this and the given number.
    *
    * @param a The number to be compared with.
    * @return -1 if the absolute value of this number is less, 0 if it's equal, 1 if it's greater.
    * @complexity O(n)
    */
  def compareAbsTo(a: BigInt): Int = {
    if (len > a.len) return 1
    if (len < a.len) return -1
    var i = len - 1
    while ( {
      i >= 0
    }) {
      if (dig(i) != a.dig(i)) if ((dig(i) & BigInt.mask) > (a.dig(i) & BigInt.mask)) return 1
      else return -1 {
        i -= 1; i + 1
      }
    }
    0
  }

  /**
    * Compares the value of this and the given number.
    *
    * @param a The number to be compared with.
    * @return -1 if the value of this number is less, 0 if it's equal, 1 if it's greater.
    * @complexity O(n)
    */
  override def compareTo(a: BigInt): Int = {
    if (sign < 0) {
      if (a.sign < 0 || a.isZero) return -compareAbsTo(a)
      return -1
    }
    if (a.sign > 0 || a.isZero) return compareAbsTo(a)
    1
  }

  /**
    * Tests equality of this number and the given one.
    *
    * @param a The number to be compared with.
    * @return true if the two numbers are equal, false otherwise.
    * @complexity O(n)
    */
  def equals(a: BigInt): Boolean = {
    if (len != a.len) return false
    if (isZero && a.isZero) return true
    if ((sign ^ a.sign) < 0) return false
    //In case definition of sign would change...
    var i = 0
    while ( {
      i < len
    }) {
      if (dig(i) != a.dig(i)) return false {
        i += 1; i - 1
      }
    }
    true
  }

  /** {@inheritDoc }
    */
  override def equals(o: Any): Boolean = {
    if (o.isInstanceOf[BigInt]) return this == o.asInstanceOf[BigInt]
    false
  } //Todo: Equality on other Number objects?
  override def hashCode: Int = {
    var hash = 0
    //Todo: Opt and improve.
    var i = 0
    while ( {
      i < len
    }) hash = (31 * hash + (dig(i) & BigInt.mask)).toInt {
      i += 1; i - 1
    }
    sign * hash //relies on 0 --> hash==0.
  }

  /** {@inheritDoc }
    * Returns this BigInt as a {@code byte}.
    *
    * @return { @code sign * (this & 0x7F)}
    */
  override def byteValue: Byte = (sign * (dig(0) & 0x7F)).toByte

  /** {@inheritDoc }
    * Returns this BigInt as a {@code short}.
    *
    * @return { @code sign * (this & 0x7FFF)}
    */
  override def shortValue: Short = (sign * (dig(0) & 0x7FFF)).toShort

  /** {@inheritDoc }
    * Returns this BigInt as an {@code int}.
    *
    * @return { @code sign * (this & 0x7FFFFFFF)}
    */
  override def intValue: Int = sign * (dig(0) & 0x7FFFFFFF) //relies on that sign always is either 1/-1.
  /** {@inheritDoc }
    * Returns this BigInt as a {@code long}.
    *
    * @return { @code sign * (this & 0x7FFFFFFFFFFFFFFF)}
    */
  override def longValue: Long = if (len == 1) sign * (dig(0) & BigInt.mask)
  else sign * ((dig(1) & 0x7FFFFFFFL) << 32 | (dig(0) & BigInt.mask))

  /** {@inheritDoc }
    * Returns this BigInt as a {@code float}.
    *
    * @return the most significant 24 bits in the mantissa (the highest order bit obviously being implicit),
    *         the exponent value which will be consistent for { @code BigInt}s up to 128 bits (should it not fit it'll be calculated modulo 256),
    *                                                                 and the sign bit set if this number is negative.
    */
  override def floatValue: Float = {
    val s = Integer.numberOfLeadingZeros(dig(len - 1))
    if (len == 1 && s >= 8) return sign * dig(0)
    var bits = dig(len - 1) //Mask out the 24 MSBits.
    if (s <= 8) bits >>>= 8 - s
    else bits = bits << s - 8 | dig(len - 2) >>> 32 - (s - 8) //s-8==additional bits we need.
    bits ^= 1L << 23 //The leading bit is implicit, cancel it out.
    val exp = (((32 - s + 32L * (len - 1)) - 1 + 127) & 0xFF).toInt
    bits |= exp << 23 //Add exponent.
    bits |= sign & (1 << 31) //Add sign-bit.
    Float.intBitsToFloat(bits)
  }

  /** {@inheritDoc }
    * Returns this BigInt as a {@code double}.
    *
    * @return the most significant 53 bits in the mantissa (the highest order bit obviously being implicit),
    *         the exponent value which will be consistent for { @code BigInt}s up to 1024 bits (should it not fit it'll be calculated modulo 2048),
    *                                                                 and the sign bit set if this number is negative.
    */
  override def doubleValue: Double = {
    if (len == 1) return sign * (dig(0) & BigInt.mask)
    val s = Integer.numberOfLeadingZeros(dig(len - 1))
    if (len == 2 && 32 - s + 32 <= 53) return sign * (dig(1).toLong << 32 | (dig(0) & BigInt.mask))
    var bits = dig(len - 1).toLong << 32 | (dig(len - 2) & BigInt.mask) //Mask out the 53 MSBits.
    if (s <= 11) bits >>>= 11 - s
    else bits = bits << s - 11 | dig(len - 3) >>> 32 - (s - 11) //s-11==additional bits we need.
    bits ^= 1L << 52
    val exp = ((32 - s + 32L * (len - 1)) - 1 + 1023) & 0x7FF
    bits |= exp << 52
    bits |= sign.toLong & (1L << 63)
    Double.longBitsToDouble(bits)
  }

  /**
    * Increases the magnitude of this number.
    *
    * @param a The amount of the increase (treated as unsigned).
    * @complexity O(n)
    * @amortized O(1)
    */
  private def uaddMag(a: Int) = {
    val tmp = (dig(0) & BigInt.mask) + (a & BigInt.mask)
    dig(0) = tmp.toInt
    if ((tmp >>> 32) != 0) {
      var i = 1
      while ( {
        i < len && {
          dig(i) += 1; dig(i)
        } == 0
      }) {
        i += 1; i - 1
      }
      if (i == len) {
        if (len == dig.length) realloc()
        dig({
          len += 1; len - 1
        }) = 1
      }
    }
  }

  /**
    * Decreases the magnitude of this number.
    * If s > this behaviour is undefined.
    *
    * @param s The amount of the decrease (treated as unsigned).
    * @complexity O(n)
    * @amortized O(1)
    */
  private def usubMag(s: Int) = {
    val dif = (dig(0) & BigInt.mask) - (s & BigInt.mask)
    dig(0) = dif.toInt
    if ((dif >> 32) != 0) {
      var i = 1
      while ( {
        dig(i) == 0
      }) {
        {
          dig(i) -= 1; dig(i)
        }
        {
          i += 1; i - 1
        }
      }
      if ( {
        dig(i) -= 1; dig(i)
      } == 0 && i + 1 == len) {
        len -= 1; len
      }
    }
  }

  /**
    * Adds an unsigned int to this number.
    *
    * @param a The amount to add (treated as unsigned).
    * @complexity O(n)
    * @amortized O(1)
    */
  def uadd(a: Int): Unit = {
    if (sign < 0) {
      if (len > 1 || (dig(0) & BigInt.mask) > (a & BigInt.mask)) {
        usubMag(a)
        return
      }
      sign = 1
      dig(0) = a - dig(0)
      return
    }
    uaddMag(a)
  }

  /**
    * Subtracts an unsigned int from this number.
    *
    * @param s The amount to subtract (treated as unsigned).
    * @complexity O(n)
    * @amortized O(1)
    */
  def usub(s: Int): Unit = {
    if (sign < 0) {
      uaddMag(s)
      return
    }
    if (len == 1 && (dig(0) & BigInt.mask) < (s & BigInt.mask)) {
      sign = -1
      dig(0) = s - dig(0)
      return
    }
    usubMag(s)
  }

  /**
    * Multiplies this number with an unsigned int.
    *
    * @param mul The amount to multiply (treated as unsigned).
    * @complexity O(n)
    */
  def umul(mul: Int): Unit = {
    if (mul == 0) {
      setToZero()
      return
      //To be removed?}
      var carry = 0
      val m = mul & BigInt.mask
      var i = 0
      while ( {
        i < len
      }) {
        carry = (dig(i) & BigInt.mask) * m + carry
        dig(i) = carry.toInt
        carry >>>= 32
        {
          i += 1; i - 1
        }
      }
      if (carry != 0) {
        if (len == dig.length) realloc()
        dig({
          len += 1; len - 1
        }) = carry.toInt
      }
    } //mul is interpreted as unsigned
    /**
      * Divides this number with an unsigned int and returns the remainder.
      *
      * @param div The amount to divide with (treated as unsigned).
      * @return The absolute value of the remainder as an unsigned int.
      * @complexity O(n)
      */
    def udiv(div: Int) = if (div < 0) safeUdiv(div)
    else unsafeUdiv(div) //returns the unsigned remainder!
    // Assumes div > 0.
    private def unsafeUdiv(div: Int): Int

    =
    {
      val d = div & BigInt.mask
      var rem = 0
      var i = len - 1
      while ( {
        i >= 0
      }) {
        rem <<= 32
        rem = rem + (dig(i) & BigInt.mask)
        dig(i) = (rem / d).toInt //Todo: opt?
        rem = rem % d
        {
          i -= 1; i + 1
        }
      }
      if (dig(len - 1) == 0 && len > 1) {
        len -= 1; len
      }
      if (len == 1 && dig(0) == 0) sign = 1
      return rem.toInt
    }

    // Assumes div < 0.
    private def safeUdiv(div: Int): Int

    =
    {
      val d = div & BigInt.mask
      val hbit = Long.MIN_VALUE
      var hq = (hbit - 1) / d
      if (hq * d + d == hbit) {
        hq += 1; hq
      }
      val hrem = hbit - hq * d
      var rem = 0
      var i = len - 1
      while ( {
        i >= 0
      }) {
        rem = (rem << 32) + (dig(i) & BigInt.mask)
        val q = (hq & rem >> 63) + ((rem & hbit - 1) + (hrem & rem >> 63)) / d
        rem = rem - q * d
        dig(i) = q.toInt
        {
          i -= 1; i + 1
        }
      }
      if (dig(len - 1) == 0 && len > 1) {
        len -= 1; len
      }
      if (len == 1 && dig(0) == 0) sign = 1
      return rem.toInt
    }

    /**
      * Modulos this number with an unsigned int.
      * I.e. sets this number to this % mod.
      *
      * @param mod The amount to modulo with (treated as unsigned).
      * @complexity O(n)
      */
    def urem(mod: Int) = if (mod < 0) safeUrem(mod)
    else unsafeUrem(mod)

    // Assumes mod > 0.
    private def unsafeUrem(mod: Int): Unit

    =
    {
      var rem = 0
      val d = mod & BigInt.mask
      var i = len - 1
      while ( {
        i >= 0
      }) {
        rem <<= 32
        rem = (rem + (dig(i) & BigInt.mask)) % d
        {
          i -= 1; i + 1
        }
      }
      len = 1
      dig(0) = rem.toInt
      if (dig(0) == 0) sign = 1
    }

    // Assumes mod < 0.
    private def safeUrem(mod: Int): Unit

    =
    {
      val d = mod & BigInt.mask
      val hbit = Long.MIN_VALUE
      // Precompute hrem = (1<<63) % d
      // I.e. the remainder caused by the highest bit.
      var hrem = (hbit - 1) % d
      if ( {
        hrem += 1; hrem
      } == d) hrem = 0
      var rem = 0
      var i = len - 1
      while ( {
        i >= 0
      }) {
        rem = (rem << 32) + (dig(i) & BigInt.mask)
        // Calculate rem %= d.
        // Do this by calculating the lower 63 bits and highest bit separately.
        // The highest bit remainder only gets added if it's set.
        rem = ((rem & hbit - 1) + (hrem & rem >> 63)) % d
        // The addition is safe and cannot overflow.
        // Because hrem < 2^32 and there's at least one zero bit in [62,32] if bit 63 is set.
        {
          i -= 1; i + 1
        }
      }
      len = 1
      dig(0) = rem.toInt
      if (dig(0) == 0) sign = 1
    }

    private def uaddMag(a: Long): Unit

    =
    {
      if (dig.length <= 2) {
        realloc(3)
        len = 2
      }
      val ah = a >>> 32
      val al = a & BigInt.mask
      var carry = (dig(0) & BigInt.mask) + al
      dig(0) = carry.toInt
      carry >>>= 32
      carry = (dig(1) & BigInt.mask) + ah + carry
      dig(1) = carry.toInt
      if ((carry >> 32) != 0) {
        var i = 2
        while ( {
          i < len && {
            dig(i) += 1; dig(i)
          } == 0
        }) {
          i += 1; i - 1
        }
        if (i == len) {
          if (len == dig.length) realloc()
          dig({
            len += 1; len - 1
          }) = 1
        }
      }
      else if (len == 2 && dig(1) == 0) {
        len -= 1; len
      }
    }

    private def usubMag(s: Long): Unit

    =
    {
      val sh = s >>> 32
      val sl = s & BigInt.mask
      var dif = (dig(0) & BigInt.mask) - sl
      dig(0) = dif.toInt
      dif >>= 32
      dif = (dig(1) & BigInt.mask) - sh + dif
      dig(1) = dif.toInt
      if ((dif >> 32) != 0) {
        var i = 2
        while ( {
          dig(i) == 0
        }) {
          {
            dig(i) -= 1; dig(i)
          }
          {
            i += 1; i - 1
          }
        }
        if ( {
          dig(i) -= 1; dig(i)
        } == 0 && i + 1 == len) {
          len -= 1; len
        }
      }
      if (len == 2 && dig(1) == 0) {
        len -= 1; len
      }
    }

    /**
      * Adds an unsigned long to this number.
      *
      * @param a The amount to add (treated as unsigned).
      * @complexity O(n)
      * @amortized O(1)
      */
    def uadd(a: Long) = if (sign < 0) {
      val ah = a >>> 32
      val al = a & BigInt.mask
      if (len > 2 || len == 2 && ((dig(1) & BigInt.mask) > ah || (dig(1) & BigInt.mask) == ah && (dig(0) & BigInt.mask) >= al) || ah == 0 && (dig(0) & BigInt.mask) >= al) {
        usubMag(a)
        return
      }
      if (dig.length == 1) realloc(2)
      if (len == 1) dig({
        len += 1; len - 1
      }) = 0
      var dif = al - (dig(0) & BigInt.mask)
      dig(0) = dif.toInt
      dif >>= 32
      dif = ah - (dig(1) & BigInt.mask) + dif
      dig(1) = dif.toInt
      //dif>>32 != 0 should be impossible
      if (dif == 0) {
        len -= 1; len
      }
      sign = 1
    }
    else uaddMag(a) //Refactor? Similar to usub.
    /**
      * Subtracts an unsigned long from this number.
      *
      * @param a The amount to subtract (treated as unsigned).
      * @complexity O(n)
      * @amortized O(1)
      */
    def usub(a: Long) = if (sign > 0) {
      val ah = a >>> 32
      val al = a & BigInt.mask
      if (len > 2 || len == 2 && ((dig(1) & BigInt.mask) > ah || (dig(1) & BigInt.mask) == ah && (dig(0) & BigInt.mask) >= al) || ah == 0 && (dig(0) & BigInt.mask) >= al) {
        usubMag(a)
        return
      }
      if (dig.length == 1) realloc(2)
      if (len == 1) dig({
        len += 1; len - 1
      }) = 0
      var dif = al - (dig(0) & BigInt.mask)
      dig(0) = dif.toInt
      dif >>= 32
      dif = ah - (dig(1) & BigInt.mask) + dif
      dig(1) = dif.toInt
      if (dif == 0) {
        len -= 1; len
      }
      sign = -1
    }
    else uaddMag(a) //Fix parameter name
    /**
      * Multiplies this number with an unsigned long.
      *
      * @param mul The amount to multiply (treated as unsigned).
      * @complexity O(n)
      */
    def umul(mul: Long) = {
      if (mul == 0) {
        setToZero()
        return
      }
      if (len + 2 >= dig.length) realloc(2 * len + 1)
      val mh = mul >>> 32
      val ml = mul & BigInt.mask
      var carry = 0
      var next = 0
      var tmp = 0L
      var i = 0
      while ( {
        i < len
      }) {
        carry = carry + next //Could this overflow?
        tmp = (dig(i) & BigInt.mask) * ml
        next = (dig(i) & BigInt.mask) * mh
        dig(i) = (tmp + carry).toInt
        carry = (tmp >>> 32) + (carry >>> 32) + ((tmp & BigInt.mask) + (carry & BigInt.mask) >>> 32)
        {
          i += 1; i - 1
        }
      }
      carry = carry + next
      dig({
        len += 1; len - 1
      }) = carry.toInt
      dig({
        len += 1; len - 1
      }) = (carry >>> 32).toInt
      while ( {
        len > 1 && dig(len - 1) == 0
      }) {
        len -= 1; len
      }
    }

    /**
      * Divides this number with an unsigned long and returns the remainder.
      *
      * @param div The amount to divide with (treated as unsigned).
      * @return The absolute value of the remainder as an unsigned long.
      * @complexity O(n)
      */
    def udiv(div: Long) = {
      if (div == (div & BigInt.mask)) return udiv(div.toInt) & BigInt.mask
      if (len == 1) {
        val tmp = dig(0) & BigInt.mask
        setToZero()
        return tmp
      }
      val s = Integer.numberOfLeadingZeros((div >>> 32).toInt)
      val dh = div >>> 32 - s
      val dl = (div << s) & BigInt.mask
      val hbit = Long.MIN_VALUE
      var u2 = 0
      var u1 = dig(len - 1) >>> 32 - s
      var u0 = (dig(len - 1) << s | dig(len - 2) >>> 32 - s) & BigInt.mask
      if (s == 0) {
        u1 = 0
        u0 = dig(len - 1) & BigInt.mask
      }
      var j = len - 2
      while ( {
        j >= 0
      }) {
        u2 = u1
        u1 = u0
        u0 = if (s > 0 && j > 0) (dig(j) << s | dig(j - 1) >>> 32 - s) & BigInt.mask
        else (dig(j) << s) & BigInt.mask
        var k = (u2 << 32) + u1
        //Unsigned division is a pain in the ass! ='(
        var qhat = (k >>> 1) / dh << 1
        var t = k - qhat * dh
        if (t + hbit >= dh + hbit) {
          qhat += 1; qhat - 1
        }
        // qhat = (u[j+n]*b + u[j+n-1])/v[n-1];
        var rhat = k - qhat * dh
        while ( {
          qhat + hbit >= (1L << 32) + hbit || qhat * dl + hbit > (rhat << 32) + u0 + hbit
        }) { //Unsigned comparison.
          qhat -= 1
          rhat = rhat + dh
          if (rhat + hbit >= (1L << 32) + hbit) break
          //todo: break is not supported}
          // Multiply and subtract. Unfolded loop.
          var p = qhat * dl
          t = u0 - (p & BigInt.mask)
          u0 = t & BigInt.mask
          k = (p >>> 32) - (t >> 32)
          p = qhat * dh
          t = u1 - k - (p & BigInt.mask)
          u1 = t & BigInt.mask
          k = (p >>> 32) - (t >> 32)
          t = u2 - k
          u2 = t & BigInt.mask
          dig(j) = qhat.toInt // Store quotient digit. If we subtracted too much, add back.
          if (t < 0) {
            dig(j) -= 1 //Unfolded loop.
            t = u0 + dl
            u0 = t & BigInt.mask
            t >>>= 32
            t = u1 + dh + t
            u1 = t & BigInt.mask
            t >>>= 32
            u2 += t & BigInt.mask
          }
          {
            j -= 1; j + 1
          }
        }
        len -= 1
        dig(len) = 0
        if (len > 1 && dig(len - 1) == 0) {
          len -= 1; len
        }
        val tmp = u1 << 32 - s | u0 >>> s
        return if (s == 0) tmp
        else u2 << 64 - s | tmp
      } //Adaption of general div to long.
      /**
        * Modulos this number with an unsigned long.
        * I.e. sets this number to this % mod.
        *
        * @param mod The amount to modulo with (treated as unsigned).
        * @complexity O(n)
        */
      def urem(mod: Long) = {
        val rem = udiv(mod) //todo: opt?
        len = 2
        dig(0) = rem.toInt
        if (rem == (rem & BigInt.mask)) {
          len -= 1
          return
          //if(dig[0]==0) sign = 1;}
          dig(1) = (rem >>> 32).toInt
        }

        /**
          * Adds an int to this number.
          *
          * @param add The amount to add.
          * @complexity O(n)
          */
        def add(add: Int) = if (add < 0) usub(-add)
        else uadd(add) //Has not amortized O(1) due to the risk of alternating +1 -1 on continuous sequence of 1-set bits.
        /**
          * Subtracts an int from this number.
          *
          * @param sub The amount to subtract.
          * @complexity O(n)
          */
        def sub(sub: Int) = if (sub < 0) uadd(-sub)
        else usub(sub)

        /**
          * Multiplies this number with an int.
          *
          * @param mul The amount to multiply with.
          * @complexity O(n)
          */
        def mul(mul: Int) = {
          if (isZero) return
          if (mul < 0) {
            sign = -sign
            umul(-mul)
          }
          else umul(mul)
        }

        /**
          * Divides this number with an int.
          *
          * @param div The amount to divide with.
          * @complexity O(n)
          * @return the signed remainder.
          */
        def div(div: Int) = {
          if (isZero) return 0
          if (div < 0) {
            sign = -sign
            return -sign * udiv(-div)
          }
          sign * udiv(div)
        }

        /**
          * Adds a long to this number.
          *
          * @param add The amount to add.
          * @complexity O(n)
          */
        def add(add: Long) = if (add < 0) usub(-add)
        else uadd(add)

        /**
          * Subtracts a long from this number.
          *
          * @param sub The amount to subtract.
          * @complexity O(n)
          */
        def sub(sub: Long) = if (sub < 0) uadd(-sub)
        else usub(sub)

        /**
          * Multiplies this number with a long.
          *
          * @param mul The amount to multiply with.
          * @complexity O(n)
          */
        def mul(mul: Long) = {
          if (isZero) return //remove?
          if (mul < 0) {
            sign = -sign
            umul(-mul)
          }
          else umul(mul)
        }

        /**
          * Divides this number with a {@code long}.
          *
          * @param div The amount to divide with.
          * @complexity O(n)
          * @return the signed remainder.
          */
        def div(div: Long) = {
          if (isZero) return 0
          if (div < 0) {
            sign = -sign
            return -sign * udiv(-div)
          }
          sign * udiv(div)
        }

        /**
          * Increases the magnitude of this number by the given magnitude array.
          *
          * @param v    The magnitude array of the increase.
          * @param vlen The length (number of digits) of the increase.
          * @complexity O(n)
          */
        private def addMag(v: Array[Int], vlen: Int): Unit

        =
        {
          var ulen = len
          var u = dig //ulen <= vlen
          if (vlen < ulen) {
            u = v
            v = dig
            ulen = vlen
            vlen = len
          }
          if (vlen > dig.length) realloc(vlen + 1)
          var carry = 0
          var i = 0
          while ( {
            i < ulen
          }) {
            carry = (u(i) & BigInt.mask) + (v(i) & BigInt.mask) + carry
            dig(i) = carry.toInt
            carry >>>= 32
            {
              i += 1; i - 1
            }
          }
          if (vlen > len) {
            System.arraycopy(v, len, dig, len, vlen - len)
            len = vlen
          }
          if (carry != 0) { //carry==1
            while ( {
              i < len && {
                dig(i) += 1; dig(i)
              } == 0
            }) {
              i += 1; i - 1
            }
            if (i == len) { //vlen==len
              if (len == dig.length) realloc()
              dig({
                len += 1; len - 1
              }) = 1
            }
          }
        }

        /**
          * Decreases the magnitude of this number by the given magnitude array.
          * Behaviour is undefined if u > |this|.
          *
          * @param u    The magnitude array of the decrease.
          * @param vlen The length (number of digits) of the decrease.
          * @complexity O(n)
          */
        private def subMag(u: Array[Int], ulen: Int): Unit

        =
        {
          val vlen = len
          val v = dig
          //Assumes vlen=len and v=dig
          var dif = 0
          var i = 0
          while ( {
            i < ulen
          }) {
            dif = (v(i) & BigInt.mask) - (u(i) & BigInt.mask) + dif
            dig(i) = dif.toInt
            dif >>= 32
            {
              i += 1; i - 1
            }
          }
          if (dif != 0) {
            while ( {
              dig(i) == 0
            }) {
              {
                dig(i) -= 1; dig(i)
              }
              {
                i += 1; i - 1
              }
            }
            if ( {
              dig(i) -= 1; dig(i)
            } == 0 && i + 1 == len) len = ulen
          }
          while ( {
            len > 1 && dig(len - 1) == 0
          }) {
            len -= 1; len
          }
        }

        /**
          * Adds a BigInt to this number.
          *
          * @param a The number to add.
          * @complexity O(n)
          */
        def add(a: BigInt) = {
          if (sign == a.sign) {
            addMag(a.dig, a.len)
            return
          }
          if (compareAbsTo(a) >= 0) {
            subMag(a.dig, a.len)
            //if(len==1 && dig[0]==0) sign = 1;
            return
          }
          val v = a.dig
          val vlen = a.len
          if (dig.length < vlen) realloc(vlen + 1)
          sign = -sign
          var dif = 0
          var i = 0
          while ( {
            i < len
          }) {
            dif = (v(i) & BigInt.mask) - (dig(i) & BigInt.mask) + dif
            dig(i) = dif.toInt
            dif >>= 32
            {
              i += 1; i - 1
            }
          }
          if (vlen > len) {
            System.arraycopy(v, len, dig, len, vlen - len)
            len = vlen
          }
          if (dif != 0) {
            while ( {
              i < vlen && dig(i) == 0
            }) {
              {
                dig(i) -= 1; dig(i)
              }
              {
                i += 1; i - 1
              }
            }
            if ( {
              dig(i) -= 1; dig(i)
            } == 0 && i + 1 == len) {
              len -= 1; len
            }
          }
          //if(i==vlen) should be impossible
        }

        /**
          * Subtracts a BigInt from this number.
          *
          * @param a The number to subtract.
          * @complexity O(n)
          */
        def sub(a: BigInt) = {
          if (sign != a.sign) {
            addMag(a.dig, a.len)
            return
          }
          if (compareAbsTo(a) >= 0) {
            subMag(a.dig, a.len)
            return
          }
          val v = a.dig
          val vlen = a.len
          if (dig.length < vlen) realloc(vlen + 1)
          sign = -sign
          var dif = 0
          var i = 0
          while ( {
            i < len
          }) {
            dif = (v(i) & BigInt.mask) - (dig(i) & BigInt.mask) + dif
            dig(i) = dif.toInt
            dif >>= 32
            {
              i += 1; i - 1
            }
          }
          if (vlen > len) {
            System.arraycopy(v, len, dig, len, vlen - len)
            len = vlen
          }
          if (dif != 0) {
            while ( {
              i < vlen && dig(i) == 0
            }) {
              {
                dig(i) -= 1; dig(i)
              }
              {
                i += 1; i - 1
              }
            }
            if ( {
              dig(i) -= 1; dig(i)
            } == 0 && i + 1 == len) {
              len -= 1; len
            }
          }
        } //Fix naming.
        /**
          * Multiplies this number by the given BigInt.
          * Chooses the appropriate algorithm with regards to the size of the numbers.
          *
          * @param mul The number to multiply with.
          * @complexity O(n^2) - O(n log n)
          **/
        def mul(mul: BigInt) = if (isZero)
        else if (mul.isZero) setToZero()
        else if (mul.len <= 2 || len <= 2) {
          sign *= mul.sign
          if (mul.len == 1) umul(mul.dig(0))
          else if (len == 1) {
            val tmp = dig(0)
            assign(mul.dig, mul.len)
            umul(tmp)
          }
          else if (mul.len == 2) umul(mul.dig(1).toLong << 32 | (mul.dig(0) & BigInt.mask))
          else {
            val tmp = dig(1).toLong << 32 | (dig(0) & BigInt.mask)
            assign(mul.dig, mul.len)
            umul(tmp)
          }
        }
        else if (len < 128 || mul.len < 128 || len.toLong * mul.len < 1 _000_000) smallMul(mul) //Remove overhead?
        else if (Math.max(len, mul.len) < 20000) karatsuba(mul, false) //Tune thresholds and remove hardcode.
        else karatsuba(mul, true)

        /**
          * Multiplies this number by the given (suitably small) BigInt.
          * Uses a quadratic algorithm which is often suitable for smaller numbers.
          *
          * @param mul The number to multiply with.
          * @complexity O(n^2)
          **/
        def smallMul(mul: BigInt) = {
          if (isZero) return
          if (mul.isZero) {
            setToZero()
            return
          }
          sign *= mul.sign
          var ulen = len
          var vlen = mul.len
          var u = dig
          var v = mul.dig
          if (vlen < ulen) {
            u = v
            v = dig
            ulen = vlen
            vlen = len
          }
          val res = BigInt.naiveMul(u, ulen, v, vlen) //Todo remove function overhead.
          dig = res
          len = res.length
          if (res(len - 1) == 0) {
            len -= 1; len
          }
        }

        /**
          * Multiplies this number by the given BigInt using the Karatsuba algorithm.
          *
          * @param mul The number to multiply with.
          * @complexity O(n^1.585)
          **/
        def karatsuba(mul: BigInt) = karatsuba(mul, false) //Fix naming?
        /**
          * Multiplies this number by the given BigInt using the Karatsuba algorithm.
          * The caller can choose to use a parallel version which is more suitable for larger numbers.
          *
          * @param mul      The number to multiply with.
          * @param parallel true if we should try to parallelize the algorithm, false if we shouldn't.
          * @complexity O(n^1.585)
          **/
        def karatsuba(mul: BigInt, parallel: Boolean) = {
          if (mul.dig.length < len) mul.realloc(len)
          else if (dig.length < mul.len) realloc(mul.len)
          if (mul.len < len) {
            var i = mul.len
            while ( {
              i < len
            }) mul.dig(i) = 0 {
              i += 1; i - 1
            }
          }
          if (len < mul.len) {
            var i = len
            while ( {
              i < mul.len
            }) dig(i) = 0 {
              i += 1; i - 1
            }
          }
          val mlen = Math.max(len, mul.len)
          var res = null
          if (!parallel) res = BigInt.kmul(dig, mul.dig, 0, mlen)
          else {
            val pool = Executors.newFixedThreadPool(12)
            try res = BigInt.pmul(dig, mul.dig, 0, mlen, 1, pool)
            catch {
              case e: Exception =>
                System.err.println(e)
            }
            pool.shutdown()
          }
          len = len + mul.len
          while ( {
            res(len - 1) == 0
          }) {
            len -= 1; len
          }
          dig = res
          sign *= mul.sign
        } //Not fully tested on small numbers... Fix naming?
        /**
          * Divides this number by the given BigInt.
          * Division by zero is undefined.
          *
          * @param div The number to divide with.
          * @complexity O(n^2)
          **/
        def div(div: BigInt) = {
          if (div.len == 1) {
            sign *= div.sign
            udiv(div.dig(0))
            return
          }
          val tmp = compareAbsTo(div)
          if (tmp < 0) {
            setToZero()
            return
          }
          if (tmp == 0) {
            uassign(1, sign * div.sign)
            return
          }
          val q = new Array[Int](len - div.len + 1)
          if (len == dig.length) realloc(len + 1) //We need an extra slot.
          div(dig, div.dig, len, div.len, q)
          dig = q
          len = q.length
          while ( {
            len > 1 && dig(len - 1) == 0
          }) {
            len -= 1; len
          }
          sign *= div.sign
        }

        /**
          * Sets this number to the remainder r satisfying q*div + r = this, where q = floor(this/div).
          *
          * @param div The number to use in the division causing the remainder.
          * @complexity O(n^2)
          **/
        def rem(div: BigInt) = { // -7/-3 = 2, 2*-3 + -1
          // -7/3 = -2, -2*3 + -1
          // 7/-3 = -2, -2*-3 + 1
          // 7/3 = 2, 2*3 + 1
          if (div.len == 1) {
            urem(div.dig(0))
            return
          }
          val tmp = compareAbsTo(div)
          if (tmp < 0) return
          if (tmp == 0) {
            setToZero()
            return
          }
          val q = new Array[Int](len - div.len + 1)
          if (len == dig.length) realloc(len + 1)
          div(dig, div.dig, len, div.len, q)
          len = div.len
          while ( {
            dig(len - 1) == 0
          }) {
            len -= 1; len
          }
        }

        /**
          * Divides this number by the given BigInt and returns the remainder.
          * Division by zero is undefined.
          *
          * @param div The number to divide with.
          * @return The remainder.
          * @complexity O(n^2)
          **/
        def divRem(div: BigInt) = {
          var tmp = sign
          if (div.len == 1) {
            sign *= div.sign
            return new BigInt(tmp, udiv(div.dig(0)))
          }
          tmp = compareAbsTo(div)
          if (tmp < 0) {
            val cpy = new BigInt(sign, dig, len)
            dig = new Array[Int](2)
            len = 1 //setToZero()
            return cpy
          }
          if (tmp == 0) {
            uassign(1, sign *= div.sign)
            return new BigInt(1, 0)
          }
          val q = new Array[Int](len - div.len + 1)
          if (len == dig.length) realloc(len + 1)
          div(dig, div.dig, len, div.len, q)
          val r = dig
          dig = q
          len = q.length
          while ( {
            len > 1 && dig(len - 1) == 0
          }) {
            len -= 1; len
          }
          tmp = div.len
          while ( {
            tmp > 1 && r(tmp - 1) == 0
          }) {
            tmp -= 1; tmp
          }
          sign *= div.sign
          new BigInt(sign / div.sign, r, tmp)
        }

        /**
          * Divides the first magnitude u[0..m) by v[0..n) and stores the resulting quotient in q.
          * The remainder will be stored in u, so u will be destroyed.
          * u[] must have room for an additional element, i.e. u[m] is a legal access.
          *
          * @param u The first magnitude array, the dividend.
          * @param v The second magnitude array, the divisor.
          * @param m The length of the first array.
          * @param n The length of the second array.
          * @param q An array of length at least n-m+1 where the quotient will be stored.
          * @complexity O(m*n)
          */
        private def div(u: Array[Int], v: Array[Int], m: Int, n: Int, q: Array[Int]): Unit

        =
        { //Hacker'sDelight's implementation of Knuth's Algorithm D
          val b = 1L << 32
          // Number base (32 bits).
          var qhat = 0L
          // Estimated quotient digit.
          var rhat = 0L
          // A remainder.
          var p = 0L
          // Product of two digits.
          var s = 0
          var i = 0
          var j = 0
          var t = 0L
          var k = 0L
          // Normalize by shifting v left just enough so that
          // its high-order bit is on, and shift u left the
          // same amount.  We may have to append a high-order
          // digit on the dividend; we do that unconditionally.
          s = Integer.numberOfLeadingZeros(v(n - 1))
          if (s > 0) { //In Java (x<<32)==(x<<0) so...
            i = n - 1
            while ( {
              i > 0
            }) v(i) = (v(i) << s) | (v(i - 1) >>> 32 - s) {
              i -= 1; i + 1
            }
            v(0) = v(0) << s
            u(m) = u(m - 1) >>> 32 - s
            i = m - 1
            while ( {
              i > 0
            }) u(i) = (u(i) << s) | (u(i - 1) >>> 32 - s) {
              i -= 1; i + 1
            }
            u(0) = u(0) << s
          }
          val dh = v(n - 1) & BigInt.mask
          val dl = v(n - 2) & BigInt.mask
          val hbit = Long.MIN_VALUE
          j = m - n
          while ( {
            j >= 0
          }) { //Main loop
            // Compute estimate qhat of q[j].
            k = u(j + n) * b + (u(j + n - 1) & BigInt.mask) //Unsigned division is a pain in the ass! ='(
            qhat = (k >>> 1) / dh << 1
            t = k - qhat * dh
            if (t + hbit >= dh + hbit) {
              qhat += 1; qhat - 1
            }
            rhat = k - qhat * dh
            while ( {
              qhat + hbit >= b + hbit || qhat * dl + hbit > b * rhat + (u(j + n - 2) & BigInt.mask) + hbit
            }) {
              qhat = qhat - 1
              rhat = rhat + dh
              if (rhat + hbit >= b + hbit) break //todo: break is not supported}
              // Multiply and subtract.
              k = 0
              i = 0
              while ( {
                i < n
              }) {
                p = qhat * (v(i) & BigInt.mask)
                t = (u(i + j) & BigInt.mask) - k - (p & BigInt.mask)
                u(i + j) = t.toInt
                k = (p >>> 32) - (t >> 32)
                {
                  i += 1; i - 1
                }
              }
              t = (u(j + n) & BigInt.mask) - k
              u(j + n) = t.toInt
              q(j) = qhat.toInt
              if (t < 0) {
                q(j) = q(j) - 1
                k = 0
                i = 0
                while ( {
                  i < n
                }) {
                  t = (u(i + j) & BigInt.mask) + (v(i) & BigInt.mask) + k
                  u(i + j) = t.toInt
                  k = t >>> 32 //>>
                  {
                    i += 1; i - 1
                  }
                }
                u(j + n) += k.toInt
              }
              {
                j -= 1; j + 1
              }
            }
            if (s > 0) { //Unnormalize v[].
              i = 0
              while ( {
                i < n - 1
              }) v(i) = v(i) >>> s | v(i + 1) << 32 - s {
                i += 1; i - 1
              }
              v(n - 1) >>>= s
              //Unnormalize u[].
              i = 0
              while ( {
                i < m
              }) u(i) = u(i) >>> s | u(i + 1) << 32 - s {
                i += 1; i - 1
              }
              u(m) >>>= s
            }
          }

          /**
            * Converts this number into a string of radix 10.
            *
            * @return The string representation of this number in decimal.
            * @complexity O(n^2)
            **/
          override def toString: String

          =
          {
            if (isZero) return "0"
            var top = len * 10 + 1
            val buf = new Array[Char](top)
            util.Arrays.fill(buf, '0')
            val cpy = util.Arrays.copyOf(dig, len)
            while ( {
              true
            }) {
              val j = top
              var tmp = toStringDiv
              while ( {
                tmp > 0
              }) {
                buf({
                  top -= 1; top
                }) += tmp % 10 //TODO: Optimize.
                tmp /= 10
              }
              if (len == 1 && dig(0) == 0) {
                break //todo: break is not supported}
                else
                {
                  top = j - 13
                }
              }
              if (sign < 0) buf({
                top -= 1; top
              }) = '-'
              System.arraycopy(cpy, 0, dig, 0, len = cpy.length)
              return new String(buf, top, buf.length - top)
            }

            // Divides the number by 10^13 and returns the remainder.
            // Does not change the sign of the number.
            private def toStringDiv: Long

            =
            {
              val pow5 = 1 _220_703_125
              val pow2 = 1 << 13
              var nextq = 0
              var rem = 0
              var i = len - 1
              while ( {
                i > 0
              }) {
                rem = (rem << 32) + (dig(i) & BigInt.mask)
                val q = (rem / pow5).toInt
                rem = rem % pow5
                dig(i) = nextq | q >>> 13
                nextq = q << 32 - 13
                {
                  i -= 1; i + 1
                }
              }
              rem = (rem << 32) + (dig(0) & BigInt.mask)
              val mod2 = dig(0) & pow2 - 1
              dig(0) = nextq | (rem / pow5 >>> 13).toInt
              rem = rem % pow5
              // Applies the Chinese Remainder Theorem.
              // -67*5^13 + 9983778*2^13 = 1
              val pow10 = pow5.toLong * pow2
              rem = (rem - pow5 * (mod2 - rem) % pow10 * 67) % pow10
              if (rem < 0) rem += pow10
              if (dig(len - 1) == 0 && len > 1) if (dig({
                len -= 1; len
              } - 1) == 0 && len > 1) {
                len -= 1; len
              }
              return rem
            }

            /**
              * Shifts this number left by the given amount (less than 32) starting at the given digit,
              * i.e. the first (<len) digits are left untouched.
              *
              * @param shift The amount to shift.
              * @param first The digit to start shifting from.
              * @complexity O(n)
              */
            private def smallShiftLeft(shift: Int, first: Int): Unit

            =
            {
              var res = dig
              if ((dig(len - 1) << shift >>> shift) != dig(len - 1)) { //Overflow?
                if ( {
                  len += 1; len
                } > dig.length) res = new Array[Int](len + 1) //realloc(len+1);
                else dig(len - 1) = 0
              }
              var nxt = if (len > dig.length) 0
              else dig(len - 1)
              var i = len - 1
              while ( {
                i > first
              }) res(i) = nxt << shift | (nxt = dig(i - 1)) >>> 32 - shift {
                i -= 1; i + 1
              }
              res(first) = nxt << shift
              dig = res
            }

            /**
              * Shifts this number right by the given amount (less than 32).
              *
              * @param shift The amount to shift.
              * @complexity O(n)
              */
            private def smallShiftRight(shift: Int): Unit

            =
            {
              var nxt = dig(0)
              var i = 0
              while ( {
                i < len - 1
              }) dig(i) = nxt >>> shift | (nxt = dig(i + 1)) << 32 - shift {
                i += 1; i - 1
              }
              if ((dig(len - 1) >>>= shift) == 0 && len > 1) {
                len -= 1; len
              }
            }

            /**
              * Shifts this number left by 32*shift, i.e. moves each digit shift positions to the left.
              *
              * @param shift The number of positions to move each digit.
              * @complexity O(n)
              */
            private def bigShiftLeft(shift: Int): Unit

            =
            {
              if (len + shift > dig.length) {
                val res = new Array[Int](len + shift + 1)
                System.arraycopy(dig, 0, res, shift, len)
                dig = res
              }
              else {
                System.arraycopy(dig, 0, dig, shift, len)
                var i = 0
                while ( {
                  i < shift
                }) dig(i) = 0 {
                  i += 1; i - 1
                }
              }
              len += shift
            }

            /**
              * Shifts this number right by 32*shift, i.e. moves each digit shift positions to the right.
              *
              * @param shift The number of positions to move each digit.
              * @complexity O(n)
              */
            private def bigShiftRight(shift: Int): Unit

            =
            {
              System.arraycopy(dig, shift, dig, 0, len - shift)
              //for(int i = len-shift; i<len; i++) dig[i] = 0;  dig[j >= len] are allowed to be anything.
              len -= shift
            }

            /**
              * Shifts this number left by the given amount.
              *
              * @param shift The amount to shift.
              * @complexity O(n)
              */
            def shiftLeft(shift: Int) = {
              val bigShift = shift >>> 5
              val smallShift = shift & 31
              if (bigShift > 0) bigShiftLeft(bigShift)
              if (smallShift > 0) smallShiftLeft(smallShift, bigShift)
            }

            /**
              * Shifts this number right by the given amount.
              *
              * @param shift The amount to shift.
              * @complexity O(n)
              */
            def shiftRight(shift: Int) = {
              val bigShift = shift >>> 5
              val smallShift = shift & 31
              if (bigShift > 0) bigShiftRight(bigShift)
              if (smallShift > 0) smallShiftRight(smallShift)
            }

            /**
              * Tests if the given bit in the number is set.
              *
              * @param bit The index of the bit to test.
              * @return true if the given bit is one.
              * @complexity O(n)
              */
            def testBit(bit: Int) = {
              val bigBit = bit >>> 5
              val smallBit = bit & 31
              if (bigBit >= len) return sign < 0
              if (sign > 0) return (dig(bigBit) & 1 << smallBit) != 0
              var j = 0
              while ( {
                j <= bigBit && dig(j) == 0
              }) {
                j += 1; j
              }
              if (j > bigBit) return false
              if (j < bigBit) return (dig(bigBit) & 1 << smallBit) == 0
              j = -dig(bigBit)
              (j & 1 << smallBit) != 0
            }

            /**
              * Sets the given bit in the number.
              *
              * @param bit The index of the bit to set.
              * @complexity O(n)
              */
            def setBit(bit: Int) = {
              val bigBit = bit >>> 5
              val smallBit = bit & 31
              if (sign > 0) {
                if (bigBit >= dig.length) {
                  realloc(bigBit + 1)
                  len = bigBit + 1
                }
                else if (bigBit >= len) {
                  while ( {
                    len <= bigBit
                  }) dig(len) = 0 {
                    len += 1; len - 1
                  }
                  // len = bigBit+1;
                }
                dig(bigBit) |= 1 << smallBit
              }
              else {
                if (bigBit >= len) return
                var j = 0
                while ( {
                  j <= bigBit && dig(j) == 0
                }) {
                  j += 1; j
                }
                if (j > bigBit) {
                  dig(bigBit) = -1 << smallBit
                  while ( {
                    dig(j) == 0
                  }) dig(j) = -1 {
                    j += 1; j - 1
                  }
                  dig(j) = ~(-dig(j))
                  if (j == len - 1 && dig(len - 1) == 0) {
                    len -= 1; len
                  }
                  return
                }
                if (j < bigBit) {
                  dig(bigBit) &= ~(1 << smallBit)
                  while ( {
                    dig(len - 1) == 0
                  }) {
                    len -= 1; len
                  }
                  return
                }
                j = Integer.lowestOneBit(dig(j)) // more efficient than numberOfTrailingZeros
                val k = 1 << smallBit
                if (k - j > 0) dig(bigBit) &= ~k // Unsigned compare.
                else {
                  dig(bigBit) ^= ((j << 1) - 1) ^ (k - 1)
                  dig(bigBit) |= k
                }
              }
            }

            /**
              * Clears the given bit in the number.
              *
              * @param bit The index of the bit to clear.
              * @complexity O(n)
              */
            def clearBit(bit: Int) = {
              val bigBit = bit >>> 5
              val smallBit = bit & 31
              if (sign > 0) if (bigBit < len) {
                dig(bigBit) &= ~(1 << smallBit)
                while ( {
                  dig(len - 1) == 0 && len > 1
                }) {
                  len -= 1; len
                }
              }
              else {
                if (bigBit >= dig.length) {
                  realloc(bigBit + 1)
                  len = bigBit + 1
                  dig(bigBit) |= 1 << smallBit
                  return
                }
                else if (bigBit >= len) {
                  while ( {
                    len <= bigBit
                  }) dig(len) = 0 {
                    len += 1; len - 1
                  }
                  dig(bigBit) |= 1 << smallBit
                  return
                }
                var j = 0
                while ( {
                  j <= bigBit && dig(j) == 0
                }) {
                  j += 1; j
                }
                if (j > bigBit) return
                if (j < bigBit) {
                  dig(bigBit) |= 1 << smallBit
                  return
                }
                j = Integer.lowestOneBit(dig(j))
                val k = 1 << smallBit
                if (j - k > 0) return // Unsigned compare
                if (j - k < 0) {
                  dig(bigBit) |= k
                  return
                }
                j = dig(bigBit)
                if (j == (-1 ^ k - 1)) {
                  dig(bigBit) = 0
                  j = bigBit + 1
                  while ( {
                    j < len && dig(j) == -1
                  }) dig(j) = 0 {
                    j += 1; j - 1
                  }
                  if (j == dig.length) realloc(j + 2)
                  if (j == len) {
                    dig({
                      len += 1; len - 1
                    }) = 1
                    return
                  }
                  dig(j) = -(~dig(j))
                }
                else {
                  j = Integer.lowestOneBit(j ^ (-1 ^ k - 1))
                  dig(bigBit) ^= j | (j - 1) ^ (k - 1)
                }
              }
            }

            /**
              * Flips the given bit in the number.
              *
              * @param bit The index of the bit to flip.
              * @complexity O(n)
              */
            def flipBit(bit: Int) = {
              val bigBit = bit >>> 5
              val smallBit = bit & 31
              block //todo: labels is not supported
              if (bigBit >= dig.length) {
                realloc(bigBit + 1)
                len = bigBit + 1
                dig(bigBit) ^= 1 << smallBit
              }
              else if (bigBit >= len) {
                while ( {
                  len <= bigBit
                }) dig(len) = 0 {
                  len += 1; len - 1
                }
                dig(bigBit) ^= 1 << smallBit
              }
              else if (sign > 0) dig(bigBit) ^= 1 << smallBit
              else {
                var j = 0
                while ( {
                  j <= bigBit && dig(j) == 0
                }) {
                  j += 1; j
                }
                if (j < bigBit) {
                  dig(bigBit) ^= 1 << smallBit
                  break block // todo: label break is not supported
                }
                if (j > bigBit) { // TODO: Refactor with setBit?
                  dig(bigBit) = -1 << smallBit
                  while ( {
                    dig(j) == 0
                  }) dig(j) = -1 {
                    j += 1; j - 1
                  }
                  dig(j) = ~(-dig(j))
                  if (j == len - 1 && dig(len - 1) == 0) {
                    len -= 1; len
                  }
                  return
                }
                j = Integer.lowestOneBit(dig(j))
                val k = 1 << smallBit
                if (j - k > 0) {
                  dig(bigBit) ^= ((j << 1) - 1) ^ (k - 1)
                  return
                }
                if (j - k < 0) {
                  dig(bigBit) ^= k
                  return
                }
                j = dig(bigBit)
                if (j == (-1 ^ k - 1)) { // TODO: Refactor with clearBit?
                  dig(bigBit) = 0
                  j = bigBit + 1
                  while ( {
                    j < len && dig(j) == -1
                  }) dig(j) = 0 {
                    j += 1; j - 1
                  }
                  if (j == dig.length) realloc(j + 2)
                  if (j == len) {
                    dig({
                      len += 1; len - 1
                    }) = 1
                    return
                  }
                  dig(j) = -(~dig(j))
                }
                else {
                  j = Integer.lowestOneBit(j ^ (-1 ^ k - 1))
                  dig(bigBit) ^= j | (j - 1) ^ (k - 1)
                }
              }
              while ( {
                dig(len - 1) == 0 && len > 1
              }) {
                len -= 1; len
              }
            }

            /**
              * Bitwise-ands this number with the given number, i.e. this &= mask.
              *
              * @param mask The number to bitwise-and with.
              * @complexity O(n)
              */
            def and(mask: BigInt) = if (sign > 0) {
              if (mask.sign > 0) {
                if (mask.len < len) len = mask.len
                var i = 0
                while ( {
                  i < len
                }) dig(i) &= mask.dig(i) {
                  i += 1; i - 1
                }
              }
              else {
                val mlen = Math.min(len, mask.len)
                var a = dig(0)
                var b = mask.dig(0)
                var j = 1
                while ( {
                  (a | b) == 0 && j < mlen
                }) {
                  a = dig(j)
                  b = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                if (a != 0 && b == 0) {
                  dig(j - 1) = 0
                  while ( {
                    j < mlen && mask.dig(j) == 0
                  }) dig(j) = 0 {
                    j += 1; j - 1
                  }
                  if (j < mlen) dig(j) &= -mask.dig(j)
                  else if (j == len) len = 1
                  j += 1
                }
                else if (a == 0) { // && (b!=0 || j==mlen)
                  while ( {
                    j < mlen && dig(j) == 0
                  }) {
                    j += 1; j - 1
                  }
                }
                else dig(j - 1) &= -b
                while ( {
                  j < mlen
                }) dig(j) &= ~mask.dig(j) {
                  j += 1; j - 1
                }
              }
              while ( {
                dig(len - 1) == 0 && len > 1
              }) {
                len -= 1; len
              }
            }
            else {
              val mlen = Math.min(len, mask.len)
              if (mask.sign > 0) {
                var a = dig(0)
                var b = mask.dig(0)
                var j = 1
                while ( {
                  (a | b) == 0 && j < mlen
                }) {
                  a = dig(j)
                  b = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                if (a != 0 && b == 0) {
                  dig(j - 1) = 0
                  while ( {
                    j < mlen && mask.dig(j) == 0
                  }) dig(j) = 0 {
                    j += 1; j - 1
                  }
                }
                else if (a == 0) {
                  while ( {
                    j < mlen && dig(j) == 0
                  }) {
                    j += 1; j - 1
                  }
                  if (j < mlen) dig(j) = -dig(j) & mask.dig(j)
                  j += 1
                }
                else dig(j - 1) = -a & b
                while ( {
                  j < mlen
                }) dig(j) = ~dig(j) & mask.dig(j) {
                  j += 1; j - 1
                }
                if (mask.len > len) {
                  if (mask.len > dig.length) realloc(mask.len + 2)
                  System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                }
                len = mask.len
                sign = 1
                while ( {
                  dig(len - 1) == 0 && len > 1
                }) {
                  len -= 1; len
                }
              }
              else {
                if (mask.len > len) {
                  if (mask.len > dig.length) realloc(mask.len + 2)
                  System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                }
                var a = dig(0)
                var b = mask.dig(0)
                var j = 1
                while ( {
                  (a | b) == 0
                }) {
                  a = dig(j)
                  b = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                if (a != 0 && b == 0) {
                  dig(j - 1) = 0
                  while ( {
                    j < mlen && mask.dig(j) == 0
                  }) dig(j) = 0 {
                    j += 1; j - 1
                  }
                  if (j < mlen) dig(j) = -(~(dig(j)) & -(mask.dig(j)))
                  j += 1
                }
                else if (a == 0) {
                  while ( {
                    j < mlen && dig(j) == 0
                  }) {
                    j += 1; j - 1
                  }
                  if (j < mlen) dig(j) = -(-(dig(j)) & ~(mask.dig(j)))
                  j += 1
                }
                else dig(j - 1) = -(-(a) & -(b))
                if (j <= mlen && dig(j - 1) == 0) {
                  if (j < mlen) {
                    dig(j) = -(~(dig(j) | mask.dig(j)))
                    while ( {
                      {
                        j += 1; j
                      } < mlen && dig(j - 1) == 0
                    }) dig(j) = -(~(dig(j) | mask.dig(j))) // -(~dig[j]&~mask.dig[j])}
                    if (j == mlen && dig(j - 1) == 0) {
                      val blen = Math.max(len, mask.len)
                      while ( {
                        j < blen && dig(j) == -1
                      }) dig({
                        j += 1; j - 1
                      }) = 0 // mask.dig[j]==dig[j]
                      if (j < blen) dig(j) = -(~dig(j))
                      else {
                        if (blen >= dig.length) realloc(blen + 2)
                        dig(blen) = 1
                        len = blen + 1
                        return
                      }
                      j += 1
                    }
                  }
                  while ( {
                    j < mlen
                  }) {
                    dig(j) |= mask.dig(j) // ~(~dig[j]&~mask.dig[j]);
                    {
                      j += 1; j - 1
                    }
                  }
                  if (mask.len > len) len = mask.len
                }
              }

              /**
                * Bitwise-ors this number with the given number, i.e. this |= mask.
                *
                * @param mask The number to bitwise-or with.
                * @complexity O(n)
                */
              def or(mask: BigInt) = if (sign > 0) if (mask.sign > 0) if (mask.len > len) {
                if (mask.len > dig.length) realloc(mask.len + 1)
                System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                var i = 0
                while ( {
                  i < len
                }) dig(i) |= mask.dig(i) {
                  i += 1; i - 1
                }
                len = mask.len
              }
              else {
                var i = 0
                while ( {
                  i < mask.len
                }) dig(i) |= mask.dig(i) {
                  i += 1; i - 1
                }
              }
              else {
                if (mask.len > dig.length) realloc(mask.len + 1)
                if (mask.len > len) System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                val mLen = Math.min(mask.len, len)
                var a = dig(0)
                var b = mask.dig(0)
                var j = 1
                while ( {
                  (a | b) == 0 && j < mLen
                }) {
                  a = dig(j)
                  b = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                if (a != 0 && b == 0) {
                  dig(j - 1) = -a
                  while ( {
                    mask.dig(j) == 0
                  }) dig(j) ^= -1 {
                    j += 1; j - 1
                  }
                  if (j < mLen) dig(j) = ~(dig(j) | -(mask.dig(j)))
                  else { // mask.dig[j] == dig[j]
                    dig(j) = ~(-dig(j))
                  }
                  j += 1
                }
                else if (a == 0) { // && (b!=0 || j==mLen)
                  dig(j - 1) = b
                  while ( {
                    j < mLen && dig(j) == 0
                  }) dig(j) = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                else { // a!=0 && b!=0
                  dig(j - 1) = -(a | -(b))
                }
                while ( {
                  j < mLen
                }) {
                  dig(j) = ~dig(j) & mask.dig(j) // ~(dig[j]|~mask.dig[j])
                  {
                    j += 1; j - 1
                  }
                }
                sign = -1
                len = mask.len
                while ( {
                  dig(len - 1) == 0
                }) {
                  len -= 1; len
                }
              }
              else {
                val mLen = Math.min(mask.len, len)
                var a = dig(0)
                var b = mask.dig(0)
                var j = 1
                while ( {
                  (a | b) == 0 && j < mLen
                }) {
                  a = dig(j)
                  b = mask.dig(j) {
                    j += 1; j - 1
                  }
                }
                if (mask.sign > 0) {
                  if (a != 0 && b == 0) while ( {
                    j < mLen && mask.dig(j) == 0
                  }) {
                    j += 1; j - 1
                  }
                  else if (a == 0) {
                    dig(j - 1) = -b
                    while ( {
                      j < mLen && dig(j) == 0
                    }) dig(j) = ~mask.dig(j) {
                      j += 1; j - 1
                    }
                    if (j < mLen) dig(j) = ~(-(dig(j)) | mask.dig(j))
                    else {
                      while ( {
                        dig(j) == 0
                      }) dig(j) = -1 {
                        j += 1; j - 1
                      }
                      dig(j) = ~(-dig(j))
                    }
                    j += 1
                  }
                  else dig(j - 1) = -(-(a) | b)
                  while ( {
                    j < mLen
                  }) {
                    dig(j) &= ~mask.dig(j) // ~(~dig[j]|mask.dig[j])
                    {
                      j += 1; j - 1
                    }
                  }
                }
                else {
                  if (a != 0 && b == 0) {
                    while ( {
                      j < mLen && mask.dig(j) == 0
                    }) {
                      j += 1; j - 1
                    }
                    if (j < mLen) dig(j) = ~(~(dig(j)) | -(mask.dig(j)))
                    j += 1
                  }
                  else if (a == 0) {
                    dig(j - 1) = b
                    while ( {
                      j < mLen && dig(j) == 0
                    }) dig(j) = mask.dig(j) {
                      j += 1; j - 1
                    }
                    if (j < mLen) dig(j) = ~(-(dig(j)) | ~(mask.dig(j)))
                    j += 1
                  }
                  else dig(j - 1) = -(-(a) | -(b))
                  while ( {
                    j < mLen
                  }) {
                    dig(j) &= mask.dig(j) // ~(~dig[j]|~mask.dig[j])
                    {
                      j += 1; j - 1
                    }
                  }
                  len = mLen
                }
                while ( {
                  dig(len - 1) == 0
                }) {
                  len -= 1; len
                }
              }

              /**
                * Bitwise-xors this number with the given number, i.e. this ^= mask.
                *
                *
                * @param mask The number to bitwise-xor with.
                * @complexity O(n)
                */
              def xor(mask: BigInt) = if (sign > 0) {
                if (mask.len > len) {
                  if (mask.len > dig.length) realloc(mask.len + 2)
                  System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                }
                val mlen = Math.min(len, mask.len)
                if (mask.sign > 0) {
                  var i = 0
                  while ( {
                    i < mlen
                  }) dig(i) ^= mask.dig(i) {
                    i += 1; i - 1
                  }
                }
                else {
                  var a = dig(0)
                  var b = mask.dig(0)
                  var j = 1
                  while ( {
                    (a | b) == 0 && j < mlen
                  }) {
                    a = dig(j)
                    b = mask.dig(j) {
                      j += 1; j - 1
                    }
                  }
                  if (a != 0 && b == 0) {
                    dig(j - 1) = -a
                    while ( {
                      mask.dig(j) == 0
                    }) dig(j) ^= -1 {
                      j += 1; j
                    }
                    if (j < len) dig(j) = ~(dig(j) ^ -(mask.dig(j)))
                    else dig(j) = ~(-mask.dig(j))
                    j += 1
                  }
                  else if (a == 0) dig(j - 1) = b // -(0^-b)
                  else {
                    dig(j - 1) = -(a ^ -(b))
                    while ( {
                      j < mlen && dig(j - 1) == 0
                    }) dig(j) = -(dig(j) ^ ~(mask.dig(j))) {
                      j += 1; j - 1
                    }
                    if (j >= mlen && dig(j - 1) == 0) {
                      val tmp = if (j < len) dig
                      else mask.dig
                      val blen = Math.max(len, mask.len)
                      while ( {
                        j < blen && tmp(j) == -1
                      }) dig(j) = 0 {
                        j += 1; j - 1
                      }
                      if (blen == dig.length) realloc(blen + 2) // len==blen
                      if (j == blen) {
                        dig(blen) = 1
                        len = blen + 1
                      }
                      else dig(j) = -(~tmp(j))
                      j += 1
                    }
                  }
                  while ( {
                    j < mlen
                  }) {
                    dig(j) ^= mask.dig(j) // ~(dig[j]^~mask.dig[j]);
                    {
                      j += 1; j - 1
                    }
                  }
                  sign = -1
                }
                if (mask.len > len) len = mask.len
                else while ( {
                  dig(len - 1) == 0 && len > 1
                }) {
                  len -= 1; len
                }
              }
              else {
                if (mask.len > len) {
                  if (mask.len > dig.length) realloc(mask.len + 2)
                  System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                }
                val mlen = Math.min(len, mask.len)
                if (mask.sign > 0) {
                  var a = dig(0)
                  var b = mask.dig(0)
                  var j = 1
                  while ( {
                    (a | b) == 0 && j < mlen
                  }) {
                    a = dig(j)
                    b = mask.dig(j) {
                      j += 1; j - 1
                    }
                  }
                  if (a != 0 && b == 0) while ( {
                    j < mlen && mask.dig(j) == 0
                  }) {
                    j += 1; j
                  }
                  else if (a == 0) {
                    dig(j - 1) = -b
                    while ( {
                      j < mlen && dig(j) == 0
                    }) dig(j) = ~mask.dig(j) {
                      j += 1; j - 1
                    }
                    while ( {
                      j < len && dig(j) == 0
                    }) dig({
                      j += 1; j - 1
                    }) = -1
                    if (j < mlen) dig(j) = ~(-(dig(j)) ^ mask.dig(j))
                    else dig(j) = ~(-dig(j))
                    j += 1
                  }
                  else dig(j - 1) = -(-(a) ^ b)
                  while ( {
                    j < mlen
                  }) {
                    dig(j) ^= mask.dig(j) // ~(~dig[j]^mask.dig[j]);
                    {
                      j += 1; j - 1
                    }
                  }
                }
                else {
                  var a = dig(0)
                  var b = mask.dig(0)
                  var j = 1
                  while ( {
                    (a | b) == 0 && j < mlen
                  }) {
                    a = dig(j)
                    b = mask.dig(j) {
                      j += 1; j - 1
                    }
                  }
                  if (a != 0 && b == 0) {
                    dig(j - 1) = -a
                    while ( {
                      mask.dig(j) == 0
                    }) {
                      dig(j) ^= -1 // ~dig[j]
                      {
                        j += 1; j - 1
                      }
                    }
                    if (j < len) dig(j) = ~dig(j) ^ -mask.dig(j)
                    else dig(j) = ~(-dig(j)) // dig[j]==mask.dig[j], ~0^-mask.dig[j]
                    j += 1
                  }
                  else if (a == 0) { // && b!=0
                    dig(j - 1) = -b
                    while ( {
                      j < mask.len && dig(j) == 0
                    }) dig(j) = ~mask.dig(j) {
                      j += 1; j - 1
                    }
                    while ( {
                      dig(j) == 0
                    }) dig({
                      j += 1; j - 1
                    }) = -1
                    if (j < mask.len) dig(j) = -dig(j) ^ ~mask.dig(j)
                    else dig(j) = ~(-dig(j)) // -dig[j]^~0
                    j += 1
                  }
                  else dig(j - 1) = -a ^ -b
                  while ( {
                    j < mlen
                  }) {
                    dig(j) ^= mask.dig(j) // ~dig[j]^~mask.dig[j]
                    {
                      j += 1; j - 1
                    }
                  }
                  sign = 1
                }
                if (mask.len > len) len = mask.len
                else while ( {
                  dig(len - 1) == 0 && len > 1
                }) {
                  len -= 1; len
                }
              }

              /**
                * Bitwise-and-nots this number with the given number, i.e. this &= ~mask.
                *
                * @param mask The number to bitwise-and-not with.
                * @complexity O(n)
                */
              def andNot(mask: BigInt) = {
                val mlen = Math.min(len, mask.len)
                if (sign > 0) if (mask.sign > 0) {
                  var i = 0
                  while ( {
                    i < mlen
                  }) dig(i) &= ~mask.dig(i) {
                    i += 1; i - 1
                  }
                }
                else {
                  var j = 0
                  while ( {
                    j < mlen && mask.dig(j) == 0
                  }) {
                    j += 1; j
                  }
                  if (j < mlen) {
                    dig(j) &= ~(-mask.dig(j))
                    while ( {
                      {
                        j += 1; j
                      } < mlen
                    }) dig(j) &= mask.dig(j) // ~~mask.dig[j]}
                    len = mlen
                  }
                  else {
                    if (mask.len > len) {
                      if (mask.len > dig.length) realloc(mask.len + 2)
                      System.arraycopy(mask.dig, len, dig, len, mask.len - len)
                    }
                    if (mask.sign > 0) {
                      var j = 0
                      while ( {
                        dig(j) == 0
                      }) {
                        j += 1; j
                      }
                      if (j < mlen) {
                        dig(j) = -(-(dig(j)) & ~(mask.dig(j)))
                        while ( {
                          {
                            j += 1; j
                          } < mlen && dig(j - 1) == 0
                        }) dig(j) = -(~(dig(j) | mask.dig(j)))
                        if (j == mlen && dig(j - 1) == 0) {
                          val blen = Math.max(len, mask.len)
                          while ( {
                            j < blen && dig(j) == -1
                          }) dig({
                            j += 1; j - 1
                          }) = 0
                          if (j < blen) dig(j) = -(~dig(j))
                          else {
                            if (blen >= dig.length) realloc(blen + 2)
                            dig(blen) = 1
                            len = blen + 1
                            return
                          }
                          j += 1
                        }
                        while ( {
                          j < mlen
                        }) dig(j) |= mask.dig(j) {
                          j += 1; j - 1
                        }
                        if (mask.len > len) len = mask.len
                      }
                    }
                    else {
                      var a = dig(0)
                      var b = mask.dig(0)
                      var j = 1
                      while ( {
                        j < mlen && (a | b) == 0
                      }) {
                        a = dig(j)
                        b = mask.dig(j) {
                          j += 1; j
                        }
                      }
                      if (a != 0 && b == 0) {
                        dig(j - 1) = -a
                        while ( {
                          j < mask.len && mask.dig(j) == 0
                        }) dig(j) ^= -1 {
                          j += 1; j - 1
                        }
                        if (j < len) dig(j) = ~(dig(j) | -(mask.dig(j))) // ~dig[j]&~-mask.dig[j]);
                        else dig(j) = ~(-dig(j)) // dig[j]==mask.dig[j]
                        j += 1
                      }
                      else if (a == 0) {
                        while ( {
                          j < mlen && dig(j) == 0
                        }) {
                          j += 1; j - 1
                        }
                        if (j < mlen) dig(j) = -dig(j) & mask.dig(j)
                        j += 1
                      }
                      else dig(j - 1) = -a & ~(-b)
                      while ( {
                        j < mlen
                      }) dig(j) = ~dig(j) & mask.dig(j) {
                        j += 1; j - 1
                      }
                      len = mask.len
                      sign = 1
                    }
                  }
                  while ( {
                    dig(len - 1) == 0 && len > 1
                  }) {
                    len -= 1; len
                  }
                }

                /**
                  * Inverts sign and all bits of this number, i.e. this = ~this.
                  * The identity -this = ~this + 1 holds.
                  *
                  * @complexity O(n)
                  */
                def not() = if (sign > 0) {
                  sign = -1
                  uaddMag(1)
                }
                else {
                  sign = 1
                  usubMag(1)
                }

                /** * </BitOperations> ***/
              }