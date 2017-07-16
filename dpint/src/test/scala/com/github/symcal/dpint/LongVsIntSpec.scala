package com.github.symcal.dpint

import com.github.symcal.dpint.DPInt.unsigned_less_than
import org.scalatest.{FlatSpec, Matchers}
import spire.syntax.cfor.cfor

class LongVsIntSpec extends FlatSpec with Matchers {

  def test_subtract_int32(src1: Array[Int], src2: Array[Int], dst: Array[Int], borrow_in: Int): Int = {
    var borrow_out: Long = borrow_in

    cfor(0)(_ < src1.length, _ + 1) { i =>
      val res = src1(i).toLong - src2(i).toLong - borrow_out

      dst(i) = (res & ((1L << 32) - 1L)).toInt

      borrow_out = res >> 32
    }
    borrow_out.toInt
  }

  def random_array(n: Int): Array[Int] = {
    Array.tabulate(n)(_ => scala.util.Random.nextInt)
  }

  def benchmark(n: Int): Long = {
    val arr1 = random_array(n)
    val arr2 = random_array(n)
    val init_time = System.nanoTime()
    test_subtract_int32(arr1, arr2, arr1, 1)
    System.nanoTime() - init_time
  }

  def test_subtract_long64(src1: Array[Long], src2: Array[Long], dst: Array[Long], borrow_in: Boolean): Boolean = {
    var borrow_out: Boolean = borrow_in
    cfor(0)(_ < src1.length, _ + 1) { i =>
      var sum1 = src1(i)
      if (borrow_out) {
        borrow_out = sum1 == 0L
        sum1 -= 1L
      }
      dst(i) = sum1 - src2(i)

      borrow_out = borrow_out || unsigned_less_than(sum1, dst(i))
    }
    borrow_out
  }

  def test_subtract_long63(src1: Array[Long], src2: Array[Long], dst: Array[Long], borrow_in: Long): Long = {
    var borrow: Long = borrow_in
    cfor(0)(_ < src1.length, _ + 1) { i =>
      val res = src1(i) - src2(i) - borrow
      dst(i) = res & ((1L << 63) - 1L)
      borrow = res >> 63
    }
    borrow
  }

  def test_subtract_int31(src1: Array[Int], src2: Array[Int], dst: Array[Int], borrow_in: Int): Int = {
    var borrow: Int = borrow_in
    var i = 0
    while (i < total) {
      val res = src1(i) - src2(i) - borrow
      dst(i) = res & ((1 << 31) - 1)
      borrow = res >> 31
      i += 1
    }
    borrow
  }

  def random_array_long(n: Int): Array[Long] = {
    Array.tabulate(n)(_ => scala.util.Random.nextLong)
  }

  def random_array_long63(n: Int): Array[Long] = {
    Array.tabulate(n)(_ => scala.util.Random.nextLong & ((1 << 63) - 1))
  }

  def random_array_int31(n: Int): Array[Int] = {
    Array.tabulate(n)(_ => scala.util.Random.nextInt & ((1 << 31) - 1))
  }

  def benchmark_long(n: Int): Long = {
    val arr1 = random_array_long(n)
    val arr2 = random_array_long(n)
    val init_time = System.nanoTime()
    val b = test_subtract_long64(arr1, arr2, arr1, true)
    val e = System.nanoTime() - init_time
    println(b)
    e
  }

  def benchmark_long63(n: Int): Long = {
    val arr1 = random_array_long63(n)
    val arr2 = random_array_long63(n)
    val init_time = System.nanoTime()
    val b = test_subtract_long63(arr1, arr2, arr1, 1)
    val e = System.nanoTime() - init_time
    println(b)
    e
  }

  def benchmark_int31(n: Int): Long = {
    val arr1 = random_array_int31(n)
    val arr2 = random_array_int31(n)
    val init_time = System.nanoTime()
    val b = test_subtract_int31(arr1, arr2, arr1, 1)
    val e = System.nanoTime() - init_time
    println(b)
    e
  }

  behavior of "long vs int"

  val total = 200000000

  it should "measure time for int using 32 bits" in {
    val elapsed1 = benchmark(total) / 1000000
    val elapsed2 = benchmark(total) / 1000000
    println(s"int32 array[$total] subtraction took $elapsed1 ms and $elapsed2 ms")
  }

  it should "measure time for int using 31 bits" in {
    val elapsed1 = benchmark_int31(total) / 1000000
    val elapsed2 = benchmark_int31(total) / 1000000
    println(s"int31 array[$total] subtraction took $elapsed1 ms and $elapsed2 ms")
  }

  it should "measure time for long using 64 bits" in {
    val elapsed1 = benchmark_long(total/2) / 1000000
    val elapsed2 = benchmark_long(total/2) / 1000000
    println(s"long64 array[${total/2}] subtraction took $elapsed1 ms and $elapsed2 ms")
  }

  it should "measure time for long using 63 bits" in {
    val elapsed1 = benchmark_long63(total/2) / 1000000
    val elapsed2 = benchmark_long63(total/2) / 1000000
    println(s"long63 array[${total/2}] subtraction took $elapsed1 ms and $elapsed2 ms")
  }
}
