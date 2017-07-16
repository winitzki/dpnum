package com.github.symcal.dpint

import org.scalatest.{FlatSpec, Matchers}

class MassifSpec extends FlatSpec with Matchers {

  behavior of "Massif"

  it should "create new Massif of given length" in {
    Seq[Long](0, 1, 10, 100, 1604, 94000, 200000, 500000, 1000000L,
      Massif.base_array_length,
      Massif.base_array_length * Massif.branch_array_length,
      Massif.base_array_length * Massif.branch_array_length * 2
    ).foreach { n ⇒
      println(s"Creating Massif($n)")
      val m = new Massif[Int](n, 0)
      m.length shouldEqual n
    }
  }

  // This requires -Xmx11G
  it should "create large Massif of given length" in {
    // Note: 17L << 27 is larger than signed Int, so we can't make an Array[T] of this size.
    Seq[Long](17L << 27).foreach { n ⇒
      val m = new Massif[Int](n, 0)
      m.length shouldEqual n
    }
  }
}
