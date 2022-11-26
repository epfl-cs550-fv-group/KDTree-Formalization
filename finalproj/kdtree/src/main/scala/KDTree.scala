import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

/** The indexing type, we just constraint them to `BigInt` for now.
  */
type Index = BigInt

/** The key type. Indexing on a list is painful but `stainless` provides many
  * list proofs :P
  */
type Key = List[Index]

case class IndexedKey(index: BigInt, key: List[Index]) {
  require(0 <= index && index < key.length)
}

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

def keyOrderAssoc(a: Key, b: Key, c: Key): Unit = {
  require(a.length == b.length && b.length == c.length)
  require(keyOrder(a, b) < 0)
  require(keyOrder(b, c) < 0)
  (a, b, c) match {
    case (Nil(), _, _) => {}
    case (Cons(ha, ta), Cons(hb, tb), Cons(hc, tc)) =>
      if ha == hb && hb == hc then keyOrderAssoc(ta, tb, tc)
      else if ha < hb then assert(ha < hc)
      else {}
  }
} ensuring (keyOrder(a, c) < 0)

def keyOrderAntisym(a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(keyOrder(a, b) < 0)
  (a, b) match {
    case (Cons(ha, ta), Cons(hb, tb)) =>
      if ha == hb then keyOrderAntisym(ta, tb)
      else {}
  }
} ensuring (keyOrder(b, a) > 0)

// /** Compares two keys given the first major index. Returns -1 if `a < b`, 1 if
//   * `a > b` and 0 if `a = b`
//   */
def keyOrderBy(index: BigInt, a: Key, b: Key): Int = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  val head = keyOrder(a.drop(index), b.drop(index))
  if head != 0 then head else keyOrder(a.take(index), b.take(index))
}

def keyOrderByEq(index: BigInt, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)

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

  if keyOrderBy(index, a, b) == 0 then rotatedEq(a, b, index)
  else {}
} ensuring (_ => if keyOrderBy(index, a, b) == 0 then a == b else a != b)

def keyOrderByAssoc(index: BigInt, a: Key, b: Key, c: Key): Unit = {
  require(a.length == b.length && b.length == c.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) < 0)
  require(keyOrderBy(index, b, c) < 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    if keyOrder(b.drop(index), c.drop(index)) == 0 then
      assert(keyOrder(a.drop(index), c.drop(index)) == 0)
      keyOrderAssoc(a.take(index), b.take(index), c.take(index))
    else {}
  else if keyOrder(b.drop(index), c.drop(index)) == 0 then {} else
    keyOrderAssoc(a.drop(index), b.drop(index), c.drop(index))
} ensuring (keyOrderBy(index, a, c) < 0)

def keyOrderByAntisym(index: BigInt, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) < 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    keyOrderAntisym(a.take(index), b.take(index))
  else keyOrderAntisym(a.drop(index), b.drop(index))
} ensuring (_ => keyOrderBy(index, b, a) > 0)

def lessThan(a: Key, b: IndexedKey): Boolean =
  a.length == b.key.length && keyOrderBy(b.index, a, b.key) < 0
def greaterThan(a: Key, b: IndexedKey): Boolean =
  a.length == b.key.length && keyOrderBy(b.index, a, b.key) > 0

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

  def forall(cond: Data[T] => Boolean): Boolean = this match
    case Empty() => true
    case Node(data, index, left, right) =>
      cond(data) && left.forall(cond) && right.forall(cond)

  def forallKeys(cond: Key => Boolean) = forall(data => cond(data.key))

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

  def compatible(key: Key) = this match
    case Empty()    => true
    case n: Node[T] => n.key.length == key.length

  /** Returns whether we can insert `data` into tree. */
  def compatible(data: Data[T]): Boolean = compatible(data.key)

  def insertWithRotatingIndex(data: Data[T], from: BigInt): Node[T] = {
    require(0 <= from && from < data.key.length)
    require(compatible(data))
    insertWithRotatingIndex(data, from, List(), List())
  } ensuring (r =>
    // membership condition
    r.keys.contains(data.key)
      && r.elements.contains(data.value)
      // size condition
      && old(this).size <= r.size && r.size <= old(this).size + 1
  )

  def insertWithRotatingIndex(
      data: Data[T],
      from: BigInt,
      ub: List[IndexedKey],
      lb: List[IndexedKey]
  ): Node[T] = {
    require(0 <= from && from < data.key.length)
    require(compatible(data))
    require(ub.forall(lessThan(data.key, _)))
    require(ub.forall(ik => forallKeys(k1 => lessThan(k1, ik))))
    require(lb.forall(greaterThan(data.key, _)))
    require(lb.forall(ik => forallKeys(k1 => greaterThan(k1, ik))))

    this match {
      case Empty() =>
        val r = Node(data, from, Empty(), Empty())
        listLtNode(ub, r)
        listGtNode(lb, r)
        r
      case n @ Node(d, index, left, right) =>
        listLtCondTree(ub, n)
        listGtCondTree(lb, n)
        val comp = keyOrderBy(index, data.key, d.key)
        val ik = IndexedKey(index, d.key)
        if comp < 0 then
          assert(left.forallKeys(k1 => lessThan(k1, ik)))
          listLtCondCons(ik, ub, n.left)

          // left tree
          val lt = left.insertWithRotatingIndex(
            data,
            nextIndex(data, index),
            ik :: ub,
            lb
          )
          val r = Node(d, index, lt, right)
          listLtNode(ub, r)
          listGtNode(lb, r)
          r
        else if comp > 0 then
          assert(right.forallKeys(k1 => greaterThan(k1, ik)))
          listGtCondCons(ik, lb, n.right)

          // right tree
          val rt = right.insertWithRotatingIndex(
            data,
            nextIndex(data, index),
            ub,
            ik :: lb
          )
          val r = Node(d, index, left, rt)
          listLtNode(ub, r)
          listGtNode(lb, r)
          r
        else
          // override
          keyOrderByEq(index, data.key, d.key)
          val r = Node(data, index, left, right)
          listLtNode(ub, r)
          listGtNode(lb, r)
          r
    }
  }.ensuring(r =>
    // membership condition
    r.keys.contains(data.key)
      && r.elements.contains(data.value)
      // size condition
      && old(this).size <= r.size && r.size <= old(this).size + 1
      // bound conditions
      && ub.forall(ik => r.forallKeys(k1 => lessThan(k1, ik)))
      && lb.forall(ik => r.forallKeys(k1 => greaterThan(k1, ik)))
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
  require(
    left.forallKeys(k => lessThan(k, IndexedKey(index, data.key))) &&
      right.forallKeys(k => greaterThan(k, IndexedKey(index, data.key)))
  )

  val key = data.key

  /** Returns the bounds of a node */
  def bounds: (Key, Key) = {
    val withLeft = left match
      case Empty() => (key, key)
      case Node(dl, _, _, _) =>
        combine(key, dl.key)
    right match
      case Empty() => withLeft
      case Node(dr, _, _, _) =>
        (combine(withLeft._1, dr.key)._1, combine(withLeft._2, dr.key)._2)
  } ensuring (
    // Size conditions
    (min, max) =>
      min.size == key.size && max.size == key.size
      // Coord conditions
      // && keyOrder(min, max) <= 0
      // Root node condition (hard to prove since we need associativity)
      // && keyOrder(min, key) <= 0 && keyOrder(key, max) <= 0
  )

  /** Returns a min and max combination of the two keys. */
  def combine(a: Key, b: Key): (Key, Key) = {
    require(a.size == b.size)
    a.zip(b)
      .map((a, b) => if a < b then (a, b) else (b, a))
      .unzip
  } ensuring (r => r._1.size == a.size && r._2.size == b.size)
}

/** All keys in a non-empty tree has the same length */
def allKeysSameLength[T](t: Node[T]): Unit = {
  allKeysSameLengthAs(t, t.key)
} ensuring (t.forallKeys(_.length == t.key.length))

// All keys has the same length
def allKeysSameLengthAs[T](t: Tree[T], key: Key): Unit = {
  require(t.compatible(key))
  t match
    case Empty() => {}
    case Node(data, index, left, right) => {
      allKeysSameLengthAs(left, key)
      allKeysSameLengthAs(right, key)
    }
} ensuring (t.forallKeys(_.length == key.length))

/** Appending lists hold the same conditions */
def appendCond[T](as: List[T], bs: List[T], cond: T => Boolean): Unit = {
  require(as.forall(cond(_)) && bs.forall(cond(_)))

  as match
    case Nil() => {}
    case Cons(h, t) =>
      assert(cond(h))
      appendCond(t, bs, cond)
} ensuring (_ => (as ++ bs).forall(cond(_)))

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
extension [A, B](xs: List[(A, B)]) {
  def unzip: (List[A], List[B]) = {
    xs match
      case Cons((a, b), t) =>
        val (as, bs) = t.unzip
        (a :: as, b :: bs)
      case Nil() => (Nil(), Nil())
  } ensuring (r => r._1 == xs.map(_._1) && r._2 == xs.map(_._2))
}

def listLtNode[T](xs: List[IndexedKey], t: Node[T]): Unit = {
  require(xs.forall(ik => lessThan(t.key, ik)))
  require(xs.forall(ik => t.left.forallKeys(k1 => lessThan(k1, ik))))
  require(xs.forall(ik => t.right.forallKeys(k1 => lessThan(k1, ik))))
  xs match
    case Nil() => {}
    case Cons(h, xs) =>
      assert(t.forallKeys(k1 => lessThan(k1, h)))
      listLtNode(xs, t)
} ensuring (xs.forall(ik => t.forallKeys(k1 => lessThan(k1, ik))))

def listLtCondTree[T](
    xs: List[IndexedKey],
    t: Node[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => lessThan(k1, ik)))
  )
  xs match
    case Nil() => {}
    case Cons(xh, xt) =>
      assert(t.forallKeys(k1 => lessThan(k1, xh)))
      listLtCondTree(xt, t)
} ensuring (_ =>
  xs.forall(ik => t.left.forallKeys(k1 => lessThan(k1, ik)))
    && xs.forall(ik => t.right.forallKeys(k1 => lessThan(k1, ik)))
    && xs.forall(ik => lessThan(t.key, ik))
)

def listLtCondCons[T](
    x: IndexedKey,
    xs: List[IndexedKey],
    t: Tree[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => lessThan(k1, ik)))
  )
  require(t.forallKeys(k1 => lessThan(k1, x)))
  t match
    case Empty() => {}
    case t @ Node(data, index, left, right) =>
      listLtCondTree(xs, t)
      listLtCondCons(x, xs, left)
      listLtCondCons(x, xs, right)
} ensuring (_ => (x :: xs).forall(ik => t.forallKeys(k1 => lessThan(k1, ik))))

def listGtNode[T](xs: List[IndexedKey], t: Node[T]): Unit = {
  require(xs.forall(ik => greaterThan(t.key, ik)))
  require(xs.forall(ik => t.left.forallKeys(k1 => greaterThan(k1, ik))))
  require(xs.forall(ik => t.right.forallKeys(k1 => greaterThan(k1, ik))))
  xs match
    case Nil() => {}
    case Cons(h, xs) =>
      assert(t.forallKeys(k1 => greaterThan(k1, h)))
      listGtNode(xs, t)
} ensuring (xs.forall(ik => t.forallKeys(k1 => greaterThan(k1, ik))))

def listGtCondTree[T](
    xs: List[IndexedKey],
    t: Node[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => greaterThan(k1, ik)))
  )
  xs match
    case Nil() => {}
    case Cons(xh, xt) =>
      assert(t.forallKeys(k1 => greaterThan(k1, xh)))
      listGtCondTree(xt, t)
} ensuring (_ =>
  xs.forall(ik => t.left.forallKeys(k1 => greaterThan(k1, ik)))
    && xs.forall(ik => t.right.forallKeys(k1 => greaterThan(k1, ik)))
    && xs.forall(ik => greaterThan(t.key, ik))
)

def listGtCondCons[T](
    x: IndexedKey,
    xs: List[IndexedKey],
    t: Tree[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => greaterThan(k1, ik)))
  )
  require(t.forallKeys(k1 => greaterThan(k1, x)))
  t match
    case Empty() => {}
    case t @ Node(data, index, left, right) =>
      listGtCondTree(xs, t)
      listGtCondCons(x, xs, left)
      listGtCondCons(x, xs, right)
} ensuring (_ =>
  (x :: xs).forall(ik => t.forallKeys(k1 => greaterThan(k1, ik)))
)

// extension [A](op: Option[A]) {

//   /** Checks the condition if the Option is not empty. */
//   def goodIfExists(cond: A => Boolean): Boolean = op match
//     case None()  => true
//     case Some(v) => cond(v)
// }
