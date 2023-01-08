import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod
import scala.quoted.* // imports Quotes, Expr

/** The indexing type, we just constraint them to `BigInt` for now.
  */
type Index = BigInt

/** The key type. Indexing on a list is painful but `stainless` provides many
  * list proofs :P
  */
type Key = List[Index]

case class IndexedKey(index: Index, key: List[Index]) {
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

def splitKey(index: Index, k: Key): (Key, Key) = {
  require(0 <= index && index < k.length)
  
  def recur(index: Index, k: Key): (Key, Key) = {
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
def keyOrderBy(index: Index, a: Key, b: Key): Int = {
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

def keyOrderByEq(index: Index, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)

  def rotatedEq(a: Key, b: Key, r: Index): Unit = {
    require(a.length == b.length)
    require(0 <= r && r < a.length)
    require(a.drop(r) == b.drop(r) && a.take(r) == b.take(r))
    splitEq(a, r)
    splitEq(b, r)
  } ensuring (a == b)

  def splitEq(a: Key, r: Index): Unit = {
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

def keyOrderByAssoc(index: Index, a: Key, b: Key, c: Key): Unit = {
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
def keyOrderByAssocEq(index: Index, a: Key, b: Key, c: Key): Unit = {
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

def greaterBy[T](t: Tree[T], index: Index, a: Data[T], b: Data[T]): Data[T] = {
  require(a.key.length == b.key.length)
  require(0 <= index && index < a.key.length)
  require(t.containsData(a))
  require(t.containsData(b))
  if keyOrderBy(index, a.key, b.key) <= 0 then b
  else
    keyOrderByAntisym(index, a.key, b.key)
    a
} ensuring (data =>
  t.containsData(data)
  && data.key.length == a.key.length 
  && keyOrderBy(index, a.key, data.key) <= 0
  && keyOrderBy(index, b.key, data.key) <= 0
  && (keyOrderBy(index, a.key, data.key) == 0
    || keyOrderBy(index, b.key, data.key) == 0)
)

def keyOrderByAntisym(index: Index, a: Key, b: Key): Unit = {
  require(a.length == b.length)
  require(0 <= index && index < a.length)
  require(keyOrderBy(index, a, b) > 0)
  if keyOrder(a.drop(index), b.drop(index)) == 0 then
    keyOrderAntisym(a.take(index), b.take(index))
  else keyOrderAntisym(a.drop(index), b.drop(index))
} ensuring (_ => keyOrderBy(index, b, a) < 0)
def keyOrderByAntisymNeg(index: Index, a: Key, b: Key): Unit = {
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
