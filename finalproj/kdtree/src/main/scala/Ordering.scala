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
