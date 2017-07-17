package com.github.symcal.dp

import scala.annotation.tailrec
import scala.reflect.ClassTag

import spire.syntax.cfor._

/** Potentially very large ( > 2^31) array with fractal structure.
  * New memory allocations are limited to arrays of fixed base length.
  **/
final class Massif[@specialized(Int, Long) T: ClassTag](init_length: Long, fill_value: T) {
  private[dp] var container_massif: ContainerMassif[T] = new BaseMassif(math.min(init_length, Massif.base_array_length).toInt, fill_value)

  def apply(i: Long): T = container_massif.apply(i)

  def update(i: Long, new_value: T): Unit = container_massif.update(i, new_value)

  def length: Long = container_massif.length

  def fill(x: T): Unit = container_massif.fill(x)

  @tailrec
  def realloc(new_size: Long, fill_value: T): Unit = {
    if (new_size > container_massif.max_capacity) { // Need to upgrade our level by create an upper-level `OverMassif`.
      container_massif.realloc(container_massif.max_capacity, fill_value) // Make sure it is full before inserting it into an upper-level `OverMassif`.
      val new_scale = container_massif.max_capacity
      val new_container: OverMassif[T] = new OverMassif(new_scale, fill_value)
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

private[dp] sealed trait ContainerMassif[@specialized(Int, Long) T] {
  def apply(i: Long): T

  def update(i: Long, new_value: T): Unit

  def length: Long

  def max_capacity: Long

  private[dp] def realloc(new_size: Long, fill_value: T): Unit

  def fill(x: T): Unit

  private[dp] def get_first: ContainerMassif[T]
}

private[dp] final class BaseMassif[@specialized(Int, Long) T: ClassTag](init_length: Int, fill_value: T) extends ContainerMassif[T] {
  def apply(i: Long): T = mantissa.apply(i.toInt)

  override def update(i: Long, new_value: T): Unit = mantissa.update(i.toInt, new_value)

  /** The length of the `mantissa` array that is currently being used.
    *
    */
  private var used_length: Int = init_length

  private val mantissa: Array[T] = new Array(Massif.base_array_length) // It seems that writing `Array[T]` here will introduce boxing.

  override def max_capacity: Long = Massif.base_array_length

  override def length: Long = used_length

  private[dp] override def realloc(new_size: Long, fill_value: T): Unit = {
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

  private[dp] override def get_first: ContainerMassif[T] = this

  fill(fill_value) // This is perhaps unnecessary, but for some reason, heap space is exceeded if this is not done!
}

private[dp] final class OverMassif[@specialized(Int, Long) T: ClassTag](scale: Long, fill_value: T) extends ContainerMassif[T] {
  def apply(i: Long): T = mantissa.apply((i / scale).toInt).apply(i % scale)

  /** The length of the `mantissa` array that is currently being used.
    *
    */
  private var used_length: Int = 0

  // Need to investigate: This line, while unused, causes an IllegalAccessError. Can a specialized class have `val`s?
//  val total_capacity = scale * Massif.branch_array_length

  override def max_capacity: Long = scale * Massif.branch_array_length

  private val mantissa: Array[ContainerMassif[T]] = new Array(Massif.branch_array_length)

  override def length: Long = (used_length - 1) * scale + mantissa(used_length - 1).length

  override def update(i: Long, new_value: T): Unit = mantissa.apply((i / scale).toInt).update(i % scale, new_value)

  private[dp] def set_first(m: ContainerMassif[T]): Unit = {
    mantissa.update(0, m)
    used_length = 1
  }

  override def fill(x: T): Unit = cfor(0)(_ < used_length, _ + 1) { i ⇒
    mantissa(i).fill(x)
  }

  private val new_subarray: () ⇒ ContainerMassif[T] = {
    if (scale > Massif.base_array_length)
      () ⇒ new OverMassif(scale / Massif.branch_array_length, fill_value)
    else
      () ⇒ new BaseMassif(Massif.base_array_length, fill_value)
  }

  private[dp] override def realloc(new_size: Long, fill_value: T): Unit = {
    val new_used_length = ((new_size + scale - 1) / scale).toInt
    val elements_differ = new_used_length - used_length
    if (elements_differ > 0) {
      // We need to allocate more elements of `mantissa`.
      cfor(used_length)(_ < new_used_length, _ + 1) { i ⇒
        mantissa(i) = new_subarray()
        if (i < new_used_length - 1) mantissa(i).realloc(scale, fill_value) // Make them full until last-but-one.
      }
    } else if (elements_differ < 0) {
      // We need to use fewer elements of `mantissa`.
      cfor(new_used_length)(_ < used_length, _ + 1) { i ⇒
        mantissa(i) = null
      }
    } else {
      // We need to realloc just one element of `mantissa`.
      // Nothing to do here since `used_length` remains unchanged.
    }
    used_length = new_used_length
    // At this time, `used_length` has been already updated and points to the last used element after all reallocations.
    mantissa(used_length - 1).realloc(new_size - scale * (new_used_length - 1), fill_value)
  }

  private[dp] override def get_first: ContainerMassif[T] = mantissa(0)
}

object Massif {
  final val base_array_length: Int = 1 << 12
  final val branch_array_length: Int = 1 << 11
}
