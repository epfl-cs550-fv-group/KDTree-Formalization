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

def eachLessThanEq(a: Key, b: Key): Boolean = {
  require(a.length == b.length)
  (a, b) match {
    case (Nil(), Nil()) => true
    case (Cons(ha, ta), Cons(hb, tb)) =>
      (ha <= hb) && eachLessThanEq(ta, tb)
  }
} 

def eachGreaterThanEq(a: Key, b: Key): Boolean = {
  require(a.length == b.length)
  (a, b) match {
    case (Nil(), Nil()) => true
    case (Cons(ha, ta), Cons(hb, tb)) =>
      (ha >= hb) && eachGreaterThanEq(ta, tb)
  }
}

def eachLessThanEqAppend(a0: Key, a1: Key, b0: Key, b1: Key): Unit = {
  require(a0.length == b0.length)
  require(a1.length == b1.length)
  require(!eachLessThanEq(a0, b0))

  a0 match {
    case Nil() => {
      assert(a0.isEmpty && b0.isEmpty)
      assert(a0 ++ a1 == a0 && b0 ++ b1 == b0)
    }
    case Cons(ha0, ta0) => {
      val (hb0, tb0) = (b0.head, b0.tail)
      if !(ha0 <= hb0) then 
        assert(!eachLessThanEq(a0 ++ a1, b0 ++ b1))
      else 
        assert(!eachLessThanEq(ta0, tb0))
        eachLessThanEqAppend(ta0, a1, tb0, b1)
        // IH: !eachLessThan(ta0 ++ a1, tb0 ++ b1)
        assert(!eachLessThanEq(a0 ++ a1, b0 ++ b1))
    }
  }
} ensuring (_ => !eachLessThanEq(a0 ++ a1, b0 ++ b1))


def eachLessThanEqPrepend(a0: Key, a1: Key, b0: Key, b1: Key): Unit = {
  require(a0.length == b0.length)
  require(a1.length == b1.length)
  require(!eachLessThanEq(a1, b1))

  a0 match {
    case Nil() => {
      assert(a0.isEmpty && b0.isEmpty)
      assert(a0 ++ a1 == a1 && b0 ++ b1 == b1)
    }
    case Cons(ha0, ta0) => {
      val (hb0, tb0) = (b0.head, b0.tail)
      eachLessThanEqPrepend(ta0, a1, tb0, b1)
      // IH: !eachlessThanEq(ta0 ++ a1, tb0 ++ b1)
      assert(!eachLessThanEq(a0 ++ a1, b0 ++ b1))
    }
  }
} ensuring (_ => !eachLessThanEq(a0 ++ a1, b0 ++ b1))

def eachGreaterThanEqAppend(a0: Key, a1: Key, b0: Key, b1: Key): Unit = {
  require(a0.length == b0.length)
  require(a1.length == b1.length)
  require(!eachGreaterThanEq(a0, b0))

  a0 match {
    case Nil() => {
      assert(a0.isEmpty && b0.isEmpty)
      assert(a0 ++ a1 == a0 && b0 ++ b1 == b0)
    }
    case Cons(ha0, ta0) => {
      val (hb0, tb0) = (b0.head, b0.tail)
      if !(ha0 >= hb0) then 
        assert(!eachGreaterThanEq(a0 ++ a1, b0 ++ b1))
      else 
        assert(!eachGreaterThanEq(ta0, tb0))
        eachGreaterThanEqAppend(ta0, a1, tb0, b1)
        // IH: !eachGreaterThan(ta0 ++ a1, tb0 ++ b1)
        assert(!eachGreaterThanEq(a0 ++ a1, b0 ++ b1))
    }
  }
} ensuring (_ => !eachGreaterThanEq(a0 ++ a1, b0 ++ b1))


def eachGreaterThanEqPrepend(a0: Key, a1: Key, b0: Key, b1: Key): Unit = {
  require(a0.length == b0.length)
  require(a1.length == b1.length)
  require(!eachGreaterThanEq(a1, b1))

  a0 match {
    case Nil() => {
      assert(a0.isEmpty && b0.isEmpty)
      assert(a0 ++ a1 == a1 && b0 ++ b1 == b1)
    }
    case Cons(ha0, ta0) => {
      val (hb0, tb0) = (b0.head, b0.tail)
      eachGreaterThanEqPrepend(ta0, a1, tb0, b1)
      // IH: !eachGreaterThanEq(ta0 ++ a1, tb0 ++ b1)
      assert(!eachGreaterThanEq(a0 ++ a1, b0 ++ b1))
    }
  }
} ensuring (_ => !eachGreaterThanEq(a0 ++ a1, b0 ++ b1))

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
} ensuring (r => 
  (if r == 0 then a == b else a != b)
  && (if r < 0 then !eachGreaterThanEq(a, b)
  else if r > 0 then !eachLessThanEq(a, b)
  else true)
)

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
def keyOrderAssocEq(a: Key, b: Key, c: Key): Unit = {
  require(a.length == b.length && b.length == c.length)
  require(keyOrder(a, b) <= 0)
  require(keyOrder(b, c) <= 0)
  (a, b, c) match {
    case (Nil(), _, _) => {}
    case (Cons(ha, ta), Cons(hb, tb), Cons(hc, tc)) =>
      if ha == hb && hb == hc then keyOrderAssocEq(ta, tb, tc)
      else if ha < hb then assert(ha < hc)
      else {}
  }
} ensuring (keyOrder(a, c) <= 0)

def keyOrderAntisym(a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(keyOrder(a, b) > 0)
  (a, b) match {
    case (Cons(ha, ta), Cons(hb, tb)) =>
      if ha == hb then keyOrderAntisym(ta, tb)
      else {}
  }
} ensuring (keyOrder(b, a) < 0)
def keyOrderAntisymNeg(a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(keyOrder(a, b) < 0)
  (a, b) match {
    case (Cons(ha, ta), Cons(hb, tb)) =>
      if ha == hb then keyOrderAntisymNeg(ta, tb)
      else {}
  }
} ensuring (keyOrder(b, a) > 0)

def splitKey(index: BigInt, k: Key): (Key, Key) = {
  require(0 <= index && index < k.length)
  
  def recur(index: BigInt, k: Key): (Key, Key) = {
    require(0 <= index && index < k.length)

    if index == 0 then (Nil(), k)
    else {
      k match {
        case Nil() => (Nil(), Nil())
        case Cons(h, t) => {
          if index == 1 then {
            (Cons(h, Nil()), t)
          } else { // index > 1
            val (sp0, sp1) = recur(index - 1, t)
            // IH: t == nsp0 ++ nsp1
            (h :: sp0, sp1)
          }
        }
      }  
    }
  } ensuring (r => 
    k == r._1 ++ r._2 && r._1.length == index && r._2.length == k.length - index
    && r._1 == k.take(index) && r._2 == k.drop(index)
  )

  recur(index, k)
} ensuring (r => 
  k == r._1 ++ r._2 && r._1.length == index && r._2.length == k.length - index
  && r._1 == k.take(index) && r._2 == k.drop(index)
)

// /** Compares two keys given the first major index. Returns -1 if `a < b`, 1 if
//   * `a > b` and 0 if `a = b`
//   */
def keyOrderBy(index: BigInt, a: Key, b: Key): Int = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)

  val (a0, a1) = splitKey(index, a)
  val (b0, b1) = splitKey(index, b)
  // assert(a == (a0 ++ a1) && (b == b0 ++ b1))
  assert(a0.length == b0.length && a1.length == b1.length)

  val head = keyOrder(a1, b1)
  val tail = keyOrder(a0, b0)

  if head < 0 then {
    assert(!eachGreaterThanEq(a1, b1))
    eachGreaterThanEqPrepend(a0, a1, b0, b1)    
  }
  else if head > 0 then {
    assert(!eachLessThanEq(a1, b1))
    eachLessThanEqPrepend(a0, a1, b0, b1)    
  }
  else {
    assert(head == 0)
    if tail < 0 then {
      assert(!eachGreaterThanEq(a0, b0))
      eachGreaterThanEqAppend(a0, a1, b0, b1)
    }
    else if tail > 0 then {
      assert(!eachLessThanEq(a0, b0))
      eachLessThanEqAppend(a0, a1, b0, b1)    
    }
  }
  
  if head != 0 then head else tail
} ensuring (r => 
  if r < 0 then a != b && !eachGreaterThanEq(a, b)
  else if r > 0 then a != b && !eachLessThanEq(a, b)
  else r == 0 && a == b
)

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
def keyOrderByAssocEq(index: BigInt, a: Key, b: Key, c: Key): Unit = {
  require(a.length == b.length && b.length == c.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) <= 0)
  require(keyOrderBy(index, b, c) <= 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    if keyOrder(b.drop(index), c.drop(index)) == 0 then
      assert(keyOrder(a.drop(index), c.drop(index)) == 0)
      keyOrderAssocEq(a.take(index), b.take(index), c.take(index))
    else {}
  else if keyOrder(b.drop(index), c.drop(index)) == 0 then {} else
    keyOrderAssoc(a.drop(index), b.drop(index), c.drop(index))
} ensuring (keyOrderBy(index, a, c) <= 0)

def greaterBy[T](index: Index, a: Data[T], b: Data[T]): Data[T] = {
  require(a.key.length == b.key.length)
  require(0 <= index && index < a.key.length)
  if keyOrderBy(index, a.key, b.key) <= 0 then b
  else
    keyOrderByAntisym(index, a.key, b.key)
    a
} ensuring (k =>
  k.key.length == a.key.length &&
    keyOrderBy(index, a.key, k.key) <= 0
    && keyOrderBy(index, b.key, k.key) <= 0
    && (keyOrderBy(index, a.key, k.key) == 0
      || keyOrderBy(index, b.key, k.key) == 0)
)

def keyOrderByAntisym(index: BigInt, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) > 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    keyOrderAntisym(a.take(index), b.take(index))
  else keyOrderAntisym(a.drop(index), b.drop(index))
} ensuring (_ => keyOrderBy(index, b, a) < 0)
def keyOrderByAntisymNeg(index: BigInt, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) < 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    keyOrderAntisymNeg(a.take(index), b.take(index))
  else keyOrderAntisymNeg(a.drop(index), b.drop(index))
} ensuring (_ => keyOrderBy(index, b, a) > 0)

def lessThan(a: Key, b: IndexedKey): Boolean =
  a.length == b.key.length && keyOrderBy(b.index, a, b.key) < 0
def lessThanEq(a: Key, b: IndexedKey): Boolean =
  a.length == b.key.length && keyOrderBy(b.index, a, b.key) <= 0
def greaterThan(a: Key, b: IndexedKey): Boolean =
  a.length == b.key.length && keyOrderBy(b.index, b.key, a) < 0

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

  def get(key: Key): T = {
    require(contains(key))
    this match 
      case Empty() => assert(false)
      case Node(data, index, left, right) => 
        if data.key == key then data.value
        else if left.contains(key) then left.get(key)
        else right.get(key)
  }

  def tryGet(key: Key): Option[T] = 
    if contains(key) then Some(get(key)) else None[T]()

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
        childContainsKeys(n, kl)
        val kr = right.keys
        childContainsKeys(n, kr)
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
      // consistency condition
      && equalExcept(old(this), r, data.key)
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
        assert(equalExcept(this, r, data.key))
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
          equalExceptInferFromLeft(n, r, data.key)
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
          equalExceptInferFromRight(n, r, data.key)
          r
        else
          // override
          keyOrderByEq(index, data.key, d.key)
          val r = Node(data, index, left, right)
          listLtNode(ub, r)
          listGtNode(lb, r)
          equalExceptInferFromRoot(n, r, data.key)
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
      // consistency condition
      && equalExcept(old(this), r, data.key)
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
      // consistency condition
      // && old(this).equalExcept(r, key)
  )
}

// Start of equalExcept condition definition and lemmas. 

def equalCond[T](a: Tree[T], b: Tree[T], key: Key): Boolean = 
  a.tryGet(key) == b.tryGet(key)

def equalExceptCond[T](a: Tree[T], b: Tree[T], excKey: Key, key: Key): Boolean = 
  if key != excKey then equalCond(a, b, key) else true

def equalExcept[T](a: Tree[T], b: Tree[T], excKey: Key): Boolean = 
  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  a.keys.forall(cond) && b.keys.forall(cond)

def forallEqualExceptSym[T](a: Tree[T], b: Tree[T], excKey: Key, ks: List[Key]): Unit = {
  require(ks.forall(k => equalExceptCond(a, b, excKey, k)))
    ks match {
      case Nil() => 
      case Cons(h, t) => 
        assert(equalExceptCond(a, b, excKey, h))
        assert(equalExceptCond(b, a, excKey, h))
        forallEqualExceptSym(a, b, excKey, t)
    }
} ensuring (ks.forall(k => equalExceptCond(b, a, excKey, k)))

def equalExceptSym[T](a: Tree[T], b: Tree[T], excKey: Key): Unit = {
  require(equalExcept(a, b, excKey))
  forallEqualExceptSym(a, b, excKey, a.keys)
  forallEqualExceptSym(a, b, excKey, b.keys)
} ensuring (equalExcept(b, a, excKey))

// End of equalExcept condition definition and lemmas. 

// Start of lemmas for equalExcept relation in insert and erase operations. 

def childContainsKeys[T](t: Node[T], ks: List[Key]): Unit = {
  require(ks.forall(t.left.contains) || ks.forall(t.right.contains))

  ks match {
    case Nil() => 
    case Cons(head, tail) => 
      assert(t.left.contains(head) || t.right.contains(head))
      assert(tail.forall(t.left.contains) || tail.forall(t.right.contains))
      assert(t.contains(head))
      childContainsKeys(t, tail)
  }
} ensuring (ks.forall(t.contains))

def forallNeq[T](t: Tree[T], ik: IndexedKey): Unit = {
  require(t.forallKeys(k => lessThan(k, ik)) || t.forallKeys(k => greaterThan(k, ik)))
  t match {
    case Empty() => {}
    case Node(data, index, left, right) => 
      assert(lessThan(data.key, ik) || greaterThan(data.key, ik))
      assert(data.key != ik.key)
      forallNeq(left, ik)
      forallNeq(right, ik)
  }
} ensuring (t.forallKeys(k => k != ik.key))

def leftGetToRootGet[T](t: Node[T], key: Key): Unit = {
  require(t.left.contains(key))
  assert(t.contains(key))
  forallNeq(t.left, IndexedKey(t.index, t.data.key))
  extractForAll(t.left, key, (k: Key) => k != t.data.key)
} ensuring (t.contains(key) && t.get(key) == t.left.get(key))

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

def rightGetToRootGet[T](t: Node[T], key: Key): Unit = {
  require(t.right.contains(key))
  assert(t.contains(key))
  // key != data.key
  forallNeq(t.right, IndexedKey(t.index, t.data.key))
  extractForAll(t.right, key, (k: Key) => k != t.data.key) 
  // !t.left.contains(key)
  rightContainsNotInLeft(t, key)
} ensuring (t.contains(key) && t.get(key) == t.right.get(key))

def raiseEqualExceptCondFromLeftList[T](a: Node[T], b: Node[T], excKey: Key, ks: List[Key]): Unit = {
  require(ks.forall(a.left.contains))
  require(ks.forall(k => equalExceptCond(a.left, b.left, excKey, k)))
  childContainsKeys(a, ks) // ks.forall(a.contains)
  ks match {
    case Nil() => 
    case Cons(h, t) => 
      assert(equalExceptCond(a.left, b.left, excKey, h) && t.forall(k => equalExceptCond(a.left, b.left, excKey, k)))
      assert(a.contains(h))
      if h != excKey then {
        assert(a.left.get(h) == b.left.get(h))
        leftGetToRootGet(a, h) // a.left.get(h) == a.get(h)
        leftGetToRootGet(b, h) // b.left.get(h) == b.get(h)
        assert(a.get(h) == b.get(h))
      } 
      assert(equalExceptCond(a, b, excKey, h))
      raiseEqualExceptCondFromLeftList(a, b, excKey, t)
    }
} ensuring (ks.forall(k => equalExceptCond(a, b, excKey, k)))

def raiseEqualExceptCondFromLeft[T](a: Node[T], b: Node[T], excKey: Key): Unit = {
  require(equalExcept(a.left, b.left, excKey))
  raiseEqualExceptCondFromLeftList(a, b, excKey, a.left.keys) // a.left.keys.forall(k => equalExceptCond(a, b, excKey, k))
  equalExceptSym(a.left, b.left, excKey)
  raiseEqualExceptCondFromLeftList(b, a, excKey, b.left.keys) // b.left.keys.forall(k => equalExceptCond(b, a, excKey, k))
  forallEqualExceptSym(b, a, excKey, b.left.keys) // b.left.keys.forall(k => equalExceptCond(a, b, excKey, k))
} ensuring (_ => 
  a.left.keys.forall(k => equalExceptCond(a, b, excKey, k))
  && b.left.keys.forall(k => equalExceptCond(a, b, excKey, k))
)

def raiseEqualExceptCondFromRightList[T](a: Node[T], b: Node[T], excKey: Key, ks: List[Key]): Unit = {
  require(ks.forall(a.right.contains))
  require(ks.forall(k => equalExceptCond(a.right, b.right, excKey, k)))
  childContainsKeys(a, ks) // ks.forall(a.contains)
  ks match {
    case Nil() => 
    case Cons(h, t) => 
      assert(equalExceptCond(a.right, b.right, excKey, h) && t.forall(k => equalExceptCond(a.right, b.right, excKey, k)))
      assert(a.contains(h))
      if h != excKey then {
        assert(a.right.get(h) == b.right.get(h))
        rightGetToRootGet(a, h) // a.left.get(h) == a.get(h)
        rightGetToRootGet(b, h) // b.left.get(h) == b.get(h)
        assert(a.get(h) == b.get(h))
      } 
      assert(equalExceptCond(a, b, excKey, h))
      raiseEqualExceptCondFromRightList(a, b, excKey, t)
    }
} ensuring (ks.forall(k => equalExceptCond(a, b, excKey, k)))

def raiseEqualExceptCondFromRight[T](a: Node[T], b: Node[T], excKey: Key): Unit = {
  require(equalExcept(a.right, b.right, excKey))
  raiseEqualExceptCondFromRightList(a, b, excKey, a.right.keys) 
  equalExceptSym(a.right, b.right, excKey)
  raiseEqualExceptCondFromRightList(b, a, excKey, b.right.keys)
  forallEqualExceptSym(b, a, excKey, b.right.keys)
} ensuring (_ => 
  a.right.keys.forall(k => equalExceptCond(a, b, excKey, k))
  && b.right.keys.forall(k => equalExceptCond(a, b, excKey, k))
)

def equalExceptReflect[T](t: Tree[T], excKey: Key, ks: List[Key]): Unit = {
  require(ks.forall(t.contains))
  ks match {
    case Nil() => 
    case Cons(head, tail) => 
      equalExceptCond(t, t, excKey, head)
      equalExceptReflect(t, excKey, tail)
  }  
} ensuring (ks.forall(k => equalExceptCond(t, t, excKey, k)))

def equalExceptInferFromLeft[T](a: Node[T], b: Node[T], excKey: Key): Unit = {
  require(equalExcept(a.left, b.left, excKey))
  require(a.right == b.right)
  require(a.data == b.data)
  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  // left
  raiseEqualExceptCondFromLeft(a, b, excKey)
  // right
  equalExceptReflect(a.right, excKey, a.right.keys) // a.right.keys.forall(condRight)
  equalExceptReflect(b.right, excKey, b.right.keys) // b.right.keys.forall(condRight)
  raiseEqualExceptCondFromRight(a, b, excKey) 
  // root
  assert(equalCond(a, b, a.data.key))
  assert(equalExceptCond(a, b, excKey, a.data.key))
  // conclude
  listConcatCond3(List(a.data.key), a.left.keys, a.right.keys, cond)
  assert(!a.keys.isEmpty && a.keys.forall(cond))
  listConcatCond3(List(b.data.key), b.left.keys, b.right.keys, cond)
  assert(!b.keys.isEmpty && b.keys.forall(cond))
} ensuring (equalExcept(a, b, excKey))

def equalExceptInferFromRight[T](a: Node[T], b: Node[T], excKey: Key): Unit = {
  require(equalExcept(a.right, b.right, excKey))
  require(a.left == b.left)
  require(a.data == b.data)
  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  // left
  equalExceptReflect(a.left, excKey, a.left.keys)
  equalExceptReflect(b.left, excKey, b.left.keys)
  raiseEqualExceptCondFromLeft(a, b, excKey) 
  // right
  raiseEqualExceptCondFromRight(a, b, excKey)
  // root
  assert(equalCond(a, b, a.data.key))
  assert(equalExceptCond(a, b, excKey, a.data.key))
  // conclude
  listConcatCond3(List(a.data.key), a.left.keys, a.right.keys, cond)
  assert(!a.keys.isEmpty && a.keys.forall(cond))
  listConcatCond3(List(b.data.key), b.left.keys, b.right.keys, cond)
  assert(!b.keys.isEmpty && b.keys.forall(cond))
} ensuring (equalExcept(a, b, excKey))

def equalExceptInferFromRoot[T](a: Node[T], b: Node[T], excKey: Key): Unit = {
  require(a.left == b.left)
  require(a.right == b.right)
  require(a.data.key == b.data.key && a.data.key == excKey)
  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  // left
  equalExceptReflect(a.left, excKey, a.left.keys)
  equalExceptReflect(b.left, excKey, b.left.keys)
  raiseEqualExceptCondFromLeft(a, b, excKey) 
  // right
  equalExceptReflect(a.right, excKey, a.right.keys) 
  equalExceptReflect(b.right, excKey, b.right.keys)
  raiseEqualExceptCondFromRight(a, b, excKey) 
  // root
  assert(equalExceptCond(a, b, excKey, a.data.key))
  // conclude
  listConcatCond3(List(a.data.key), a.left.keys, a.right.keys, cond)
  assert(!a.keys.isEmpty && a.keys.forall(cond))
  listConcatCond3(List(b.data.key), b.left.keys, b.right.keys, cond)
  assert(!b.keys.isEmpty && b.keys.forall(cond))
} ensuring (equalExcept(a, b, excKey))

// End of Lemmas for equalExcept relation in insert and erase operations. 

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

def listConcatCond[T](l0: List[T], l1: List[T], cond: T => Boolean): List[T] = {
  require(l0.isEmpty || (!l0.isEmpty && l0.forall(cond)))
  require(l1.isEmpty || (!l1.isEmpty && l1.forall(cond)))

  l0 match {
    case Nil() => 
      assert(l0 ++ l1 == l1)
      l1   
    case Cons(h, t) => 
      assert(l0 ++ l1 == h :: (t ++ l1))
      assert(!l0.isEmpty && l0.forall(cond))
      assert(t.isEmpty || !t.isEmpty && t.forall(cond))
      
      val r = h :: listConcatCond(t, l1, cond)
      assert(l0 ++ l1 == h :: (t ++ l1))
      assert(cond(h))
      assert(!r.isEmpty && r.forall(cond))
      r
  }
} ensuring(r => (r == l0 ++ l1) && (r.isEmpty || (!r.isEmpty && r.forall(cond))))

def listConcatCond3[T](l0: List[T], l1: List[T], l2: List[T], cond: T => Boolean): List[T] = {
  require(l0.isEmpty || (!l0.isEmpty && l0.forall(cond)))
  require(l1.isEmpty || (!l1.isEmpty && l1.forall(cond)))
  require(l2.isEmpty || (!l2.isEmpty && l2.forall(cond)))

  val v0 = listConcatCond(l0, l1, cond)
  val v1 = listConcatCond(v0, l2, cond)
  assert(v1 == l0 ++ l1 ++ l2)
  v1
} ensuring(r => (r == l0 ++ l1 ++ l2) && (r.isEmpty || (!r.isEmpty && r.forall(cond))))

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

def listLtExtractForall[T](xs: List[IndexedKey], t: Tree[T], key: Key): Unit = {
  require(xs.forall(ik => t.forallKeys(k1 => lessThan(k1, ik))))
  require(t.contains(key))
  xs match
    case Nil() => {}
    case Cons(h, xs) => {
      extractForAll(t, key, k => lessThan(k, h))
      listLtExtractForall(xs, t, key)
    }
} ensuring (xs.forall(lessThan(key, _)))

def listLeExtractForall[T](xs: List[IndexedKey], t: Tree[T], key: Key): Unit = {
  require(xs.forall(ik => t.forallKeys(k1 => lessThanEq(k1, ik))))
  require(t.contains(key))
  xs match
    case Nil() => {}
    case Cons(h, xs) => {
      extractForAll(t, key, k => lessThanEq(k, h))
      listLeExtractForall(xs, t, key)
    }
} ensuring (xs.forall(lessThanEq(key, _)))

def listGtExtractForall[T](xs: List[IndexedKey], t: Tree[T], key: Key): Unit = {
  require(xs.forall(ik => t.forallKeys(k1 => greaterThan(k1, ik))))
  require(t.contains(key))
  xs match
    case Nil() => {}
    case Cons(h, xs) => {
      extractForAll(t, key, k => greaterThan(k, h))
      listGtExtractForall(xs, t, key)
    }
} ensuring (xs.forall(greaterThan(key, _)))

def listLeNode[T](xs: List[IndexedKey], t: Node[T]): Unit = {
  require(xs.forall(ik => lessThanEq(t.key, ik)))
  require(xs.forall(ik => t.left.forallKeys(k1 => lessThanEq(k1, ik))))
  require(xs.forall(ik => t.right.forallKeys(k1 => lessThanEq(k1, ik))))
  xs match
    case Nil() => {}
    case Cons(h, xs) =>
      assert(t.forallKeys(k1 => lessThanEq(k1, h)))
      listLeNode(xs, t)
} ensuring (xs.forall(ik => t.forallKeys(k1 => lessThanEq(k1, ik))))

def listLeCondTree[T](
    xs: List[IndexedKey],
    t: Node[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => lessThanEq(k1, ik)))
  )
  xs match
    case Nil() => {}
    case Cons(xh, xt) =>
      assert(t.forallKeys(k1 => lessThanEq(k1, xh)))
      listLeCondTree(xt, t)
} ensuring (_ =>
  xs.forall(ik => t.left.forallKeys(k1 => lessThanEq(k1, ik)))
    && xs.forall(ik => t.right.forallKeys(k1 => lessThanEq(k1, ik)))
    && xs.forall(ik => lessThanEq(t.key, ik))
)

def listLeCondCons[T](
    x: IndexedKey,
    xs: List[IndexedKey],
    t: Tree[T]
): Unit = {
  require(
    xs.forall(ik => t.forallKeys(k1 => lessThanEq(k1, ik)))
  )
  require(t.forallKeys(k1 => lessThanEq(k1, x)))
  t match
    case Empty() => {}
    case t @ Node(data, index, left, right) =>
      listLeCondTree(xs, t)
      listLeCondCons(x, xs, left)
      listLeCondCons(x, xs, right)
} ensuring (_ => (x :: xs).forall(ik => t.forallKeys(k1 => lessThanEq(k1, ik))))

// extension [A](op: Option[A]) {

//   /** Checks the condition if the Option is not empty. */
//   def goodIfExists(cond: A => Boolean): Boolean = op match
//     case None()  => true
//     case Some(v) => cond(v)
// }
