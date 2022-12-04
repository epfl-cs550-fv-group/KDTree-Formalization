import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

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

  def exists(cond: Data[T] => Boolean): Boolean = this match
    case Empty() => false
    case Node(data, index, left, right) =>
      cond(data) || left.exists(cond) || right.exists(cond)

  def existsKeys(cond: Key => Boolean) = exists(data => cond(data.key))

  def contains(key: Key): Boolean = this match
    case Empty() => false
    case Node(data, index, left, right) =>
      data.key == key || left.contains(key) || right.contains(key)

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
    r.contains(data.key)
      && r.get(data.key) == data.value
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
          keyOrderByAntisym(index, data.key, d.key)
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
    r.contains(data.key)
      && r.get(data.key) == data.value
      // size condition
      && old(this).size <= r.size && r.size <= old(this).size + 1
      // bound conditions
      && ub.forall(ik => r.forallKeys(k1 => lessThan(k1, ik)))
      && lb.forall(ik => r.forallKeys(k1 => greaterThan(k1, ik)))
  )

  /** Erases a key from the tree. Returns the old tree if the key does not
    * exist.
    */
  def erase(key: Key): Tree[T] = {
    if contains(key) then erase(key, List(), List(), List())
    else this
  } ensuring (r =>
    // membership condition
    !r.contains(key)
    // size condition
      && old(this).size - 1 <= r.size && r.size <= old(this).size
  )

  /** Erases a key from the tree. The key must exist inside the tree. */
  def erase(
      key: Key,
      ub: List[IndexedKey],
      ueb: List[IndexedKey],
      lb: List[IndexedKey]
  ): Tree[T] = {
    require(contains(key))
    require(ub.forall(ik => forallKeys(k1 => lessThan(k1, ik))))
    require(ueb.forall(ik => forallKeys(k1 => lessThanEq(k1, ik))))
    require(lb.forall(ik => forallKeys(k1 => greaterThan(k1, ik))))
    decreases(size)
    this match
      case Empty() => ??? // never happens
      case n @ Node(d, index, left, right) =>
        containsIsSameLength(n, key)
        listLtCondTree(ub, n)
        listLeCondTree(ueb, n)
        listGtCondTree(lb, n)
        val ik = IndexedKey(index, d.key)
        val comp = keyOrderBy(index, key, d.key)
        if comp < 0 then
          keyOrderByEq(index, key, d.key) // key != d.key
          assert(key != d.key)
          // bounds
          assert(left.forallKeys(k1 => lessThan(k1, ik)))
          listLtCondCons(ik, ub, n.left)
          // go left
          goLeft(n, key)
          val lt = left.erase(key, ik :: ub, ueb, lb)
          val r = Node(d, index, lt, right)
          listLtNode(ub, r)
          listLeNode(ueb, r)
          listGtNode(lb, r)
          r
        else if comp > 0 then
          keyOrderByEq(index, key, d.key) // key != d.key
          assert(key != d.key)
          // bounds
          keyOrderByAntisym(index, key, d.key)
          assert(right.forallKeys(k1 => greaterThan(k1, ik)))
          listGtCondCons(ik, lb, n.right)
          // go left
          goRight(n, key)
          val rt = right.erase(key, ub, ueb, ik :: lb)
          val r = Node(d, index, left, rt)
          listLtNode(ub, r)
          listLeNode(ueb, r)
          listGtNode(lb, r)
          r
        else
          keyOrderByEq(index, key, d.key) // key != d.key
          assert(right.forallKeys(greaterThan(_, ik)))
          assert(!greaterThan(key, ik))
          extractNotContains(right, key, k => greaterThan(k, ik))
          left match {
            case Empty()    => right
            case l: Node[T] =>
              // bounds
              assert(left.forallKeys(k1 => lessThan(k1, ik)))
              listLtCondCons(ik, ub, n.left)

              val greatestLeft = l.greatestKeyBy(index)
              // prove that greatestLeft.key is still less than right tree
              extractForAll(l, greatestLeft.key, k => lessThan(k, ik))
              keyOrderByAntisymNeg(
                index,
                greatestLeft.key,
                d.key
              ) // d.key > gL.key
              forallKeysAssoc(right, index, d.key, greatestLeft.key)

              val glik = IndexedKey(index, greatestLeft.key)
              listLeCondCons(glik, ueb, l)

              val lt = l.erase(greatestLeft.key, ik :: ub, glik :: ueb, lb)
              // prove !lt.contains(key)
              // we have lt.forallKeys(lessThan(_, ik)) and !lessThan(key, ik)
              assert(!lessThan(key, ik))
              assert(lt.forallKeys(lessThan(_, ik)))
              extractNotContains(lt, key, k => lessThan(k, ik))

              forallKeysRefineIneq(lt, index, greatestLeft.key)

              val r = Node(greatestLeft, index, lt, right)
              listLtExtractForall(ub, left, greatestLeft.key)
              listLeExtractForall(ueb, left, greatestLeft.key)
              listGtExtractForall(lb, left, greatestLeft.key)
              listLtNode(ub, r)
              listLeNode(ueb, r)
              listGtNode(lb, r)
              r
          }
  } ensuring (r =>
    // membership condition
    !r.contains(key)
    // size condition
      && old(this).size - 1 == r.size
      // bound conditions
      && ub.forall(ik => r.forallKeys(k1 => lessThan(k1, ik)))
      && ueb.forall(ik => r.forallKeys(k1 => lessThanEq(k1, ik)))
      && lb.forall(ik => r.forallKeys(k1 => greaterThan(k1, ik)))
  )

  /* QUERIES */

  def query(key: Key): Option[T] =
    if contains(key) then Some(get(key)) else None()

  def get(key: Key): T = {
    require(contains(key))
    containsIsSameLength(this, key)
    this match
      case Empty() => ??? // never happens
      case n @ Node(data, index, left, right) =>
        val comp = keyOrderBy(index, key, data.key)
        if comp < 0 then
          goLeft(n, key)
          left.get(key)
        else if comp > 0 then
          keyOrderByAntisym(index, key, data.key)
          goRight(n, key)
          right.get(key)
        else
          keyOrderByEq(index, key, data.key) // key == data.key
          data.value
  }
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

  val indexedKey = IndexedKey(index, key)

  def greatestKeyBy(index: Index): Data[T] = {
    require(0 <= index && index < key.length)
    allChildrenSameLength(this)
    left match
      case Empty() =>
        right match
          case Empty() => data
          case n: Node[T] =>
            val rgt = n.greatestKeyBy(index)
            val res = greaterBy(index, data, rgt)
            forallKeysAssocEq(n, index, rgt.key, res.key)
            res
      case l: Node[T] =>
        val lgt = l.greatestKeyBy(index)
        val withL = greaterBy(index, data, lgt)
        forallKeysAssocEq(l, index, lgt.key, withL.key)
        right match
          case Empty() =>
            assert(
              right.forallKeys(lessThanEq(_, IndexedKey(index, withL.key)))
            )
            withL
          case r: Node[T] =>
            val rgt = r.greatestKeyBy(index)
            val res = greaterBy(index, withL, rgt)
            forallKeysAssocEq(r, index, rgt.key, res.key)
            keyOrderByAssocEq(index, key, withL.key, res.key)
            forallKeysAssocEq(l, index, withL.key, res.key)
            res
  } ensuring (d =>
    contains(d.key)
      && d.key.length == key.length
      && forallKeys(lessThanEq(_, IndexedKey(index, d.key)))
  )

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

/** If a key exists and is less than the root key, go left. */
def goLeft[T](t: Node[T], key: Key): Unit = {
  require(t.contains(key))
  require(lessThan(key, t.indexedKey))

  keyOrderByEq(t.index, key, t.key) // key != t.key
  assert(t.left.contains(key) || t.right.contains(key))
  if t.right.contains(key) then {
    extractForAll(t.right, key, k => greaterThan(k, t.indexedKey))
    keyOrderByAntisymNeg(t.index, t.key, key)
  } else {}
} ensuring (t.left.contains(key) && !t.right.contains(key))

/** If a key exists and is greater than the root key, go right. */
def goRight[T](t: Node[T], key: Key): Unit = {
  require(t.contains(key))
  require(greaterThan(key, t.indexedKey))

  keyOrderByEq(t.index, key, t.key) // key != t.key
  assert(t.left.contains(key) || t.right.contains(key))
  if t.left.contains(key) then {
    extractForAll(t.left, key, k => lessThan(k, t.indexedKey))
    keyOrderByAntisymNeg(t.index, t.key, key)
  } else {}
} ensuring (t.right.contains(key) && !t.left.contains(key))

def forallKeysAssocEq[T](t: Tree[T], index: Index, k1: Key, k2: Key): Unit = {
  require(0 <= index && index < k1.length && k1.length == k2.length)
  require(lessThanEq(k1, IndexedKey(index, k2)))
  require(t.forallKeys(lessThanEq(_, IndexedKey(index, k1))))
  t match
    case Empty() => {}
    case Node(data, _, left, right) =>
      keyOrderByAssocEq(index, data.key, k1, k2)
      forallKeysAssocEq(left, index, k1, k2)
      forallKeysAssocEq(right, index, k1, k2)
} ensuring (t.forallKeys(lessThanEq(_, IndexedKey(index, k2))))

def forallKeysAssoc[T](t: Tree[T], index: Index, k1: Key, k2: Key): Unit = {
  require(0 <= index && index < k1.length && k1.length == k2.length)
  require(greaterThan(k1, IndexedKey(index, k2))) // k2 < k1
  require(t.forallKeys(greaterThan(_, IndexedKey(index, k1)))) // k1 < k

  t match
    case Empty() => {}
    case Node(data, _, left, right) =>
      keyOrderByAssoc(index, k2, k1, data.key) // k2 < data.key
      forallKeysAssoc(left, index, k1, k2)
      forallKeysAssoc(right, index, k1, k2)
} ensuring (t.forallKeys(greaterThan(_, IndexedKey(index, k2))))

def forallKeysRefineIneq[T](t: Tree[T], index: Index, key: Key): Unit = {
  require(0 <= index && index < key.length)
  require(!t.contains(key))
  require(t.forallKeys(lessThanEq(_, IndexedKey(index, key))))

  val ik = IndexedKey(index, key)
  t match
    case Empty() => {}
    case Node(data, _, left, right) => {
      assert(data.key != key)
      keyOrderByEq(index, data.key, key)
      assert(lessThan(data.key, ik))
      forallKeysRefineIneq(left, index, key)
      forallKeysRefineIneq(right, index, key)
    }
} ensuring (t.forallKeys(lessThan(_, IndexedKey(index, key))))

def extractForAll[T](t: Tree[T], k: Key, cond: Key => Boolean): Unit = {
  require(t.forallKeys(cond))
  require(t.contains(k))
  t match
    case Empty() => {}
    case Node(data, index, left, right) => {
      if data.key == k then {} else if left.contains(k) then
        extractForAll(left, k, cond)
      else extractForAll(right, k, cond)
    }
} ensuring (cond(k))

def extractNotContains[T](t: Tree[T], k: Key, cond: Key => Boolean): Unit = {
  require(t.forallKeys(cond))
  require(!cond(k))
  t match
    case Empty() => {}
    case Node(data, index, left, right) =>
      assert(cond(data.key) && !cond(k))
      extractNotContains(left, k, cond)
      extractNotContains(right, k, cond)
} ensuring (!t.contains(k))

def containsIsSameLength[T](t: Tree[T], k: Key): Unit = {
  require(t.contains(k))
  decreases(t.size)
  t match
    case Empty() => {}
    case t: Node[T] =>
      if t.key == k then {} else {
        allChildrenSameLength(t)
        if t.left.contains(k) then containsIsSameLength(t.left, k)
        else containsIsSameLength(t.right, k)
      }
} ensuring (t.asInstanceOf[Node[T]].key.length == k.length)

def allChildrenSameLength[T](t: Node[T]): Unit = {
  allKeysSameLength(t)
} ensuring (
  (t.left match
    case Empty()                        => true
    case Node(data, index, left, right) => data.key.length == t.key.length
  )
    && (t.right match
      case Empty()                        => true
      case Node(data, index, left, right) => data.key.length == t.key.length
    )
)

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
    ts == xs.filter(pred)
      && fs == xs.filterNot(pred)
      && xs.size == ts.size + fs.size
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
