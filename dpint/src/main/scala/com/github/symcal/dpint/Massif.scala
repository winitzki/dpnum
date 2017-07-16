package com.github.symcal.dpint

import scala.annotation.tailrec
import scala.reflect.ClassTag

import spire.syntax.cfor._

/** Potentially very large ( > 2^31) array with fractal structure.
  * New memory allocations are limited to arrays of fixed base length.
  **/
class Massif[@specialized(Int, Long) T: ClassTag](init_length: Long, fill_value: T) {
  private var container_massif: ContainerMassif[T] = new BaseMassif[T](math.min(init_length, Massif.base_array_length).toInt, fill_value)

  def apply(i: Long): T = container_massif.apply(i)

  def update(i: Long, new_value: T): Unit = container_massif.update(i, new_value)

  def length: Long = container_massif.length

  def fill(x: T): Unit = container_massif.fill(x)

  @tailrec
  final def realloc(new_size: Long, fill_value: T): Unit = {
    if (new_size > container_massif.max_capacity) { // Need to upgrade our level by create an upper-level `OverMassif`.
      container_massif.realloc(container_massif.max_capacity, fill_value) // Make sure it is full before inserting it into an upper-level `OverMassif`.
      val new_container = new OverMassif[T](container_massif.scale * Massif.branch_array_length, fill_value)
      new_container.set_first(container_massif)
      container_massif = new_container
      realloc(new_size, fill_value) // We may need to repeat this process.
    } else if (new_size < container_massif.max_capacity / Massif.branch_array_length) { // We may need to downgrade our level.
      if (length > Massif.base_array_length) {
        // We have an `OverMassif`. Downgrade one level and realloc recursively.
        container_massif = container_massif.get_first
        realloc(new_size, fill_value)
      } else {
        // We have a `BaseMassif`.
        container_massif.realloc(new_size, fill_value)
      }
    } else { // We do not need to upgrade or downgrade our level. Let the container handle the rest of the realloc.
      container_massif.realloc(new_size, fill_value)
    }
  }

  realloc(init_length, fill_value)
}

//@specialized(Int, Long) T
sealed trait ContainerMassif[T] {
  def apply(i: Long): T

  def update(i: Long, new_value: T): Unit

  def length: Long

  val scale: Long = 1

  val max_capacity: Long = scale * Massif.base_array_length

  def realloc(new_size: Long, fill_value: T): Unit

  def fill(x: T): Unit

  def get_first: ContainerMassif[T]
}

private class BaseMassif[T: ClassTag](init_length: Int, fill_value: T) extends ContainerMassif[T] {
  def apply(i: Long): T = mantissa.apply(i.toInt)

  override def update(i: Long, new_value: T): Unit = mantissa.update(i.toInt, new_value)

  /** The length of the `mantissa` array that is currently being used.
    *
    */
  private var used_length: Int = init_length

  private val mantissa: Array[T] = new Array(Massif.base_array_length)

  override val max_capacity: Long = Massif.base_array_length

  override def length: Long = used_length

  override def realloc(new_size: Long, fill_value: T): Unit = {
    val effective_size = math.min(new_size, max_capacity).toInt
    // Fill with zeros if we are increasing the length.
    if (effective_size > used_length) {
      fill(fill_value, used_length, effective_size - used_length)
    }
    used_length = effective_size
  }

  def fill(x: T, init_offset: Int, count: Int): Unit = cfor(init_offset)(_ < init_offset + count, _ + 1) { i ⇒
    mantissa.update(i, x)
  }

  override def fill(x: T): Unit = fill(x, 0, used_length)

  override def get_first: ContainerMassif[T] = this

  fill(fill_value)
}
// [@specialized(Int, Long) T]pp[
private class OverMassif[T: ClassTag](override val scale: Long = Massif.branch_array_length, fill_value: T) extends ContainerMassif[T] {
  def apply(i: Long): T = mantissa.apply((i / scale).toInt).apply(i % scale)

  /** The length of the `mantissa` array that is currently being used.
    *
    */
  private var used_length: Int = 0

  private val mantissa: Array[ContainerMassif[T]] = new Array(Massif.branch_array_length)

  override def length: Long = (used_length - 1) * scale + mantissa(used_length - 1).length

  override def update(i: Long, new_value: T): Unit = mantissa.apply((i / scale).toInt).update(i % scale, new_value)

  def set_first(m: ContainerMassif[T]): Unit = {
    mantissa.update(0, m)
    used_length = 1
  }

  override def fill(x: T): Unit = cfor(0)(_ < used_length, _ + 1) { i ⇒
    mantissa(i).fill(x)
  }

  override def realloc(new_size: Long, fill_value: T): Unit = {
    val new_used_length = ((new_size + scale - 1) / scale).toInt
    val elements_differ = new_used_length - used_length
    if (elements_differ > 0) {
      // We need to allocate more elements of `mantissa`.
      cfor(used_length)(_ < new_used_length, _ + 1) { i ⇒
        mantissa(i) = if (scale > Massif.branch_array_length)
          new OverMassif[T](scale / Massif.branch_array_length, fill_value)
        else
          new BaseMassif[T](Massif.base_array_length, fill_value)
        if (i < new_used_length - 1) mantissa(i).realloc(scale, fill_value) // Make them full until last-but-one.
      }
    } else if (elements_differ < 0) {
      // We need to use fewer elements of `mantissa`.
      cfor(new_used_length + 1)(_ < used_length, _ + 1) { i ⇒
        mantissa(i) = null
      }
    } else {
      // We need to realloc just one element of `mantissa`.
      // Nothing to do here since `used_length` remains unchanged.
    }
    used_length = new_used_length
    // At this time, `used_length` has been already updated and points to the last used element after all reallocations.
    mantissa(used_length - 1).realloc(new_size % scale, fill_value)
  }

  override def get_first: ContainerMassif[T] = mantissa(0)
}

object Massif {
  val base_array_length: Int = 1024
  val branch_array_length: Int = 256
}