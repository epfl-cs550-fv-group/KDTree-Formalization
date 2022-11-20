import stainless.lang._
import stainless.collection._

/** The indexing type, we just constraint them to `BigInt` for now.
  */
type Index = BigInt

/** The key type. Indexing on a list is painful but `stainless` provides many
  * list proofs :P
  */
type Key = List[Index]

/** Compares two keys. Returns -1 if `a < b`, 1 if `a > b` and 0 if `a = b` */
def keyOrder(a: Key, b: Key): Int = {
  require(a.length == b.length)
  (a, b) match {
    case (Nil(), Nil()) => 0
    case (Cons(ha, ta), Cons(hb, tb)) =>
      if ha < hb then -1
      else if ha > hb then 1
      else keyOrder(ta, tb)
  }
} ensuring (r => if r == 0 then a == b else a != b)

/** Compares two keys given the first major index. Returns -1 if `a < b`, 1 if
  * `a > b` and 0 if `a = b`
  */
def keyOrderBy(index: BigInt, a: Key, b: Key): Int = {
  val k = a.length
  require(a.length == b.length)
  require(0 <= index && index < k)
  val head = keyOrder(a.drop(index), b.drop(index))
  if head != 0 then head else keyOrder(a.take(index), b.take(index))
}

def keyOrderByEq(index: BigInt, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  if keyOrderBy(index, a, b) == 0 then rotatedEq(a, b, index)
  else {}
} ensuring (_ => if keyOrderBy(index, a, b) == 0 then a == b else a != b)

def rotatedEq(a: Key, b: Key, r: BigInt): Unit = {
  require(a.length == b.length)
  require(0 <= r && r < a.length)
  require(a.drop(r) == b.drop(r) && a.take(r) == b.take(r))
  splitEq(a, r)
  splitEq(b, r)
} ensuring (a == b)

def splitEq(a: Key, r: BigInt): Unit = {
  require(0 <= r && r < a.length)
  if r == 0 then {
    assert(a.take(r) == Nil())
    assert(a.drop(r) == a)
  } else {
    assert(a.take(r).head == a.head)
    assert(a.take(r).tail == a.tail.take(r - 1))
    splitEq(a.tail, r - 1)
  }
} ensuring (a.take(r) ++ a.drop(r) == a)

/** The data part of a node.
  */
case class Data[T](key: List[Index], value: T)

/** A node in the KD-Tree.
  */
sealed trait Tree[T] {
  // BASIC OPERATIONS

  /** Size of the tree */
  def size: BigInt = this match {
    case Empty()                        => BigInt(0)
    case Node(data, index, left, right) => 1 + left.size + right.size
  } ensuring (_ >= 0)

  /** Elements of the tree */
  def elements: List[T] = this match {
    case Empty() => List()
    case Node(data, index, left, right) =>
      left.elements ++ List(data.value) ++ right.elements
  } ensuring (_.length == this.size)

  def keys: List[Key] = {
    this match
      case Empty() => List()
      case Node(data, index, left, right) =>
        List(data.key) ++ left.keys ++ right.keys
  } ensuring (ks => ks.length == this.size)

  /** Returns whether we can insert `data` into tree. */
  def compatible(data: Data[T]) = this match
    case Empty()                     => true
    case Node(d, index, left, right) => d.key.length == data.key.length

  def insertWithRotatingIndex(data: Data[T], from: BigInt): Node[T] =
    require(0 <= from && from < data.key.length)
    require(compatible(data))
    this match {
      case Empty() => Node(data, from, Empty(), Empty())
      case Node(d, index, left, right) =>
        val comp = keyOrderBy(index, data.key, d.key)
        if comp < 0 then
          // left tree
          Node(
            d,
            index,
            left.insertWithRotatingIndex(data, nextIndex(data, index)),
            right
          )
        else if comp > 0 then
          // right tree
          Node(
            d,
            index,
            left,
            right.insertWithRotatingIndex(data, nextIndex(data, index))
          )
        else
          // override
          Node(data, index, left, right)
    } ensuring (r =>
      // root condition
      (old(this) match
        case Empty()                      => r.data == data
        case Node(d0, index, left, right) => r.data == d0 || r.data == data
      )
      // membership condition
        && r.keys.contains(data.key)
        && r.elements.contains(data.value)
        // size condition
        && old(this).size <= r.size && r.size <= old(this).size + 1
    )
}

def nextIndex[T](data: Data[T], index: BigInt): BigInt = {
  require(0 <= index && index < data.key.length)
  if index + 1 == data.key.length then BigInt(0) else index + 1
} ensuring (0 <= index && index < data.key.length)

/** An empty node */
case class Empty[T]() extends Tree[T]

/** A non-empty node */
case class Node[T](data: Data[T], index: BigInt, left: Tree[T], right: Tree[T])
    extends Tree[T] {
  require(0 <= index && index < data.key.length)
  // left node must be smaller <
  require(left match
    case Empty() => true
    case Node(dl, _, _, _) =>
      dl.key.length == data.key.length &&
      keyOrderBy(index, dl.key, data.key) < 0
  )
  // right node must be larger >
  require(right match
    case Empty() => true
    case Node(dr, _, _, _) =>
      dr.key.length == data.key.length &&
      keyOrderBy(index, dr.key, data.key) > 0
  )
}

/** k-th smallest element of `xs`, ordered by `comp`. */
def kthElement[T](
    xs: List[Data[T]],
    k: BigInt,
    comp: (Key, Key) => Int
): Data[T] = {
  decreases(xs.size)
  require(0 <= k && k < xs.size)
  // Normally we pick a random element here, but for simplicity we
  // just pick the first element.
  xs match {
    case Cons(h, Nil()) => h
    case Cons(h, t) => {
      val (ls, rs) = t.strongPartition((d: Data[T]) => comp(d.key, h.key) <= 0)
      if ls.size > k then kthElement(ls, k, comp)
      else if ls.size == k then h
      else kthElement(rs, k - 1 - ls.size, comp)
    }
  }
} ensuring (r => xs.contains(r))

extension [T](xs: List[T]) {

  /** Partition, but with stronger results about result lengths. */
  def strongPartition(pred: T => Boolean): (List[T], List[T]) = {
    xs match
      case Cons(h, t) =>
        val (ts, fs) = t.strongPartition(pred)
        if pred(h) then (h :: ts, fs) else (ts, h :: fs)
      case Nil() => (Nil(), Nil())
  } ensuring ((ts, fs) =>
    ts == xs.filter(pred) && fs == xs.filterNot(
      pred
    ) && xs.size == ts.size + fs.size
  )
}
