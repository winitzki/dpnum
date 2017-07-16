package com.github.symcal.dpint

import org.scalatest.{FlatSpec, Matchers}

class MassifSpec extends FlatSpec with Matchers {

  behavior of "Massif"

  it should "create new Massif of length 1604" in {
    val m = new Massif[Int](1604, 0)
    m.length shouldEqual 1604
  }

  it should "create new Massif of length 1000" in {
    val m = new Massif[Int](1000, 0)
    m.length shouldEqual 1000
  }
}
