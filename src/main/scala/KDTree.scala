import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

/** The data part of a node.
  */
case class Data[T](key: List[Index], value: T) {
  require(key.size > 0)
}

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

  def get(key: Key): T = {
    require(contains(key))
    this match 
      case Empty() => assert(false)
      case Node(data, index, left, right) => 
        if data.key == key then data.value
        else if left.contains(key) then left.get(key)
        else right.get(key)
  }

  def query(key: Key): Option[T] = 
    if contains(key) then Some(get(key)) else None[T]()

  def containsData(data: Data[T]): Boolean = 
    contains(data.key) && get(data.key) == data.value

  /** Elements of the tree */
  def elements: List[T] = this match {
    case Empty() => List()
    case Node(data, index, left, right) =>
      left.elements ++ List(data.value) ++ right.elements
  } ensuring (_.length == this.size)

  def keys: List[Key] = {
    this match
      case Empty() => List()
      case n @ Node(data, index, left, right) =>
        assert(contains(data.key))
        val kl = left.keys 
        rootContainsChildKeys(n, kl)
        val kr = right.keys
        rootContainsChildKeys(n, kr)
        val ks = listConcatCond3(List(data.key), kl, kr, contains)
        assert(ks == List(data.key) ++ left.keys ++ right.keys)
        ks
  } ensuring (ks => 
    ks.length == this.size && ks.forall(contains))

  def compatible(key: Key) = this match
    case Empty()    => true
    case n: Node[T] => n.key.length == key.length

  /** Returns whether we can insert `data` into tree. */
  def compatible(data: Data[T]): Boolean = compatible(data.key)
}

def rightContainsNotInLeft[T](t: Node[T], key: Key): Unit = {
  require(t.right.contains(key))
  val ik = IndexedKey(t.index, t.data.key)

  assert(t.right.forallKeys(k => greaterThan(k, ik)))
  extractForAll(t.right, key, (k: Key) => greaterThan(k, ik))
  assert(greaterThan(key, ik))

  if t.left.contains(key) then 
    assert(t.left.forallKeys(k => lessThan(k, ik)))
    extractForAll(t.left, key, (k: Key) => lessThan(k, ik)) // lessThan(key, ik)
    assert(lessThan(key, ik) && greaterThan(key, ik))
    assert(keyOrderBy(ik.index, key, ik.key) < 0)
    assert(keyOrderBy(ik.index, ik.key, key) < 0)
    keyOrderByAntisymNeg(ik.index, key, ik.key) // keyOrderBy(index, ik.key, key) > 0
    assert(keyOrderBy(ik.index, ik.key, key) < 0 && keyOrderBy(ik.index, ik.key, key) > 0)
  else assert(true)

} ensuring (!t.left.contains(key))

def nextIndex[T](data: Data[T], index: BigInt): BigInt = {
  require(0 <= index && index < data.key.length)
  if index + 1 == data.key.length then BigInt(0) else index + 1
} ensuring (0 <= index && index < data.key.length)

/** An empty node */
case class Empty[T]() extends Tree[T]

/** A non-empty node */
case class Node[T](data: Data[T], index: Index, left: Tree[T], right: Tree[T])
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
    assert(this.containsData(data))
    left match
      case Empty() =>
        right match
          case Empty() => data
          case n: Node[T] =>
            val rgt = n.greatestKeyBy(index)
            rootContainsRightData(this, rgt)
            val res = greaterBy(this, index, data, rgt)
            assert(this.containsData(res))
            forallKeysAssocEq(n, index, rgt.key, res.key)
            res
      case l: Node[T] =>
        val lgt = l.greatestKeyBy(index)
        rootContainsLeftData(this, lgt)
        val withL = greaterBy(this, index, data, lgt)
        forallKeysAssocEq(l, index, lgt.key, withL.key)
        right match
          case Empty() =>
            assert(
              right.forallKeys(lessThanEq(_, IndexedKey(index, withL.key)))
            )
            withL
          case r: Node[T] =>
            val rgt = r.greatestKeyBy(index)
            rootContainsRightData(this, rgt)
            val res = greaterBy(this, index, withL, rgt)
            forallKeysAssocEq(r, index, rgt.key, res.key)
            keyOrderByAssocEq(index, key, withL.key, res.key)
            forallKeysAssocEq(l, index, withL.key, res.key)
            res
  } ensuring (d =>
      containsData(d)
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

def rootContainsLeftData[T](n: Node[T], d: Data[T]): Unit = {
  val (data, index, left, right) = (n.data, n.index, n.left, n.right)
  require(left.containsData(d))
  val ik = IndexedKey(index, data.key)
  extractForAll(left, d.key, (k: Key) => lessThan(k, ik)) // n.data.key != d.key
} ensuring (n.containsData(d))

def rootContainsRightData[T](n: Node[T], d: Data[T]): Unit = {
  val (data, index, left, right) = (n.data, n.index, n.left, n.right) 
  require(right.containsData(d))
  val ik = IndexedKey(index, data.key)
  extractForAll(right, d.key, (k: Key) => greaterThan(k, ik)) // n.data.key != d.key
  rightContainsNotInLeft(n, d.key) // !left.contains(d.key)
} ensuring (n.containsData(d))

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

