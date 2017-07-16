package com.github.symcal.dpint

import org.scalacheck.Prop.{BooleanOperators, forAll}
import org.scalacheck.{Gen, Properties}

object MassifProps extends Properties("Massif") {
  val positiveInt = Gen.choose(0, 1 << 20)

  property("correct initial length") = forAll(positiveInt) { (n: Int) ⇒
    (n > 0) ==> {
      val l = new Massif[Int](n, 0).length
//      println(s"initial length with n=$n is $l")
      l == n
    }
  }

  val smallInteger = Gen.choose(0, 100)

  property("fill array with value") = forAll(smallInteger, smallInteger, positiveInt) { (m: Int, n: Int, x: Int) ⇒
    (n > 0 && m < n) ==> (new Massif[Int](n, x).apply(m) == x)
  }

  property("write to array then read") = forAll { (x: Int, y: Int) ⇒
    val a = new Massif[Int](3, x)
    a(0) == x
    a(1) == x
    a(2) == x
    a.update(1, y)
    a(0) == x
    a(1) == y
    a(2) == x
    a.fill(y)
    a(0) == y
    a(1) == y
    a(2) == y
  }

  property("write to large array") = forAll(positiveInt) { (n0: Int) ⇒
    (n0 > 0) ==> {
      val n = n0 + 1
      val a = new Massif[Int](n, 0)
      a(n0) == 0
      a.update(n0, 123)
      a(n0) == 123
    }
  }

  property("realloc from small to big size assigns correct new length") = forAll(smallInteger, positiveInt) { (m: Int, n: Int) ⇒
    (m > 0 && n > 0) ==> {
      val a = new Massif[Int](m, 0)
      a.length == m
      a.realloc(n, 0)
      a.length == n
      a.realloc(m + 1, 0)
      a.length == m + 1
    }
  }
}
