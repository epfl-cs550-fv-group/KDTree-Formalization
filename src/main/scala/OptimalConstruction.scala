import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod
import scala.quoted.*

/** Given a list of data, construct the optimal height KD-Tree containing all
  * elements of `arr`. `arr`'s keys must be unique.
  */
def optimalConstruct[T](
    arr: List[Data[T]]
): Tree[T] = {
  require(arr.isSameSize)
  require(arr.isUnique)

  arr match
    case Nil() => Empty()
    case arr @ Cons(h, t) =>
      val key = h.key
      arr.headSameIsSame(key)
      // prove conditions 4 & 5 holds for empty list
      def recurse(xs: List[Data[T]]): Unit = {
        xs match
          case Cons(_, t) => recurse(t)
          case Nil()      => {}
      } ensuring (
        xs.forall(d => List().forall(ik => lessThan(d.key, ik)))
          && xs.forall(d => List().forall(ik => greaterThan(d.key, ik)))
      )
      recurse(arr)

      optimalConstruct(arr, 0, key, List(), List())
} ensuring (r =>
  // size conditions
  r.size == arr.size
  // optimal conditions
    && pow2(depth(r)) <= 2 * arr.size + 1
    // elem conditions
    && arr.forall(d => r.query(d.key) == Some[T](d.value))
)
def optimalConstruct[T](
    arr: List[Data[T]],
    index: BigInt,
    key: Key,
    ub: List[IndexedKey],
    lb: List[IndexedKey]
): Tree[T] = {
  require(0 <= index && index < key.length)
  require(arr.size >= 1)
  require(arr.isSameSizeAs(key))
  require(arr.isUnique)
  require(arr.forall(d => ub.forall(ik => lessThan(d.key, ik))))
  require(arr.forall(d => lb.forall(ik => greaterThan(d.key, ik))))
  decreases(arr.size)

  arr match
    case Nil() => Empty()
    case arr @ Cons(_, _) =>
      val size = arr.size
      val k = size / 2

      val (kth, less, greater) = arr.kthElementByIndex(index, k, key)
      // Trickle down conditions 4 & 5 to less & greater
      arr.containsListExtractCond(
        less,
        d => ub.forall(ik => lessThan(d.key, ik))
      )
      arr.containsListExtractCond(
        less,
        d => lb.forall(ik => greaterThan(d.key, ik))
      )
      arr.containsListExtractCond(
        greater,
        d => ub.forall(ik => lessThan(d.key, ik))
      )
      arr.containsListExtractCond(
        greater,
        d => lb.forall(ik => greaterThan(d.key, ik))
      )

      arr.listExtractForAll(kth, d => ub.forall(ik => lessThan(d.key, ik)))
      arr.listExtractForAll(kth, d => lb.forall(ik => greaterThan(d.key, ik)))

      val ik = IndexedKey(index, kth.key)

      // extends less with ik
      less.conditionListAppendLt(ik, ub)
      greater.conditionListAppendGt(ik, lb)

      val tl =
        if less.size == 0 then Empty()
        else optimalConstruct(less, nextIndex(kth, index), key, ik :: ub, lb)
      val tr =
        if greater.size == 0 then Empty()
        else optimalConstruct(greater, nextIndex(kth, index), key, ub, ik :: lb)

      // extract extended conditions
      tl.listExtractLt(ik, ub)
      tr.listExtractGt(ik, lb)

      val t = Node(kth, index, tl, tr)

      pow2Max(depth(tl), depth(tr))
      assert(pow2(depth(t)) == 2 * max(pow2(depth(tl)), pow2(depth(tr))))
      if less.size == 0 then assert(size == 1)
      else if greater.size == 0 then
        assert(size <= 2)
        if (size == 1) then {} else {
          assert(less.size == 1)
          assert(depth(tl) == 1)
          assert(depth(t) == 2)
        }
      else
        maxBound(pow2(depth(tl)), 2 * k, pow2(depth(tr)), 2 * (size - k - 1))
        assert(max(2 * k, 2 * (size - k - 1)) <= size)
        assert(2 * max(pow2(depth(tl)), pow2(depth(tr))) <= 2 * size)
        assert(pow2(depth(t)) <= 2 * arr.size)

      t.climbUp(less)
      t.climbUp(greater)
      assert(keyOrderBy(index, kth.key, kth.key) == 0)
      assert(t.query(kth.key) == Some[T](kth.value))

      t.climbUpLt(ub)
      t.climbUpGt(lb)

      tupCond(less, kth, greater, d => t.query(d.key) == Some[T](d.value))
      tup(less, kth, greater).containsListExtractCond(
        arr,
        d => t.query(d.key) == Some[T](d.value)
      )

      t
} ensuring (r =>
  // size conditions
  r.size == arr.size
  // optimal condition
    && pow2(depth(r)) <= 2 * arr.size
    // elem conditions
    && arr.forall(d => r.query(d.key) == Some[T](d.value))
    // bound conditions
    && r.forallKeys(k => ub.forall(lessThan(k, _)))
    && r.forallKeys(k => lb.forall(greaterThan(k, _)))
)

/** Depth of a tree. */
def depth[T](t: Tree[T]): BigInt = {
  t match
    case Empty() => BigInt(0)
    case Node(data, index, left, right) =>
      1 + max(depth(left), depth(right))
} ensuring (_ >= 0)

def max(a: BigInt, b: BigInt) = {
  if a < b then b else a
} ensuring (r => r >= a && r >= b && (r == a || r == b))

def maxBound(a: BigInt, am: BigInt, b: BigInt, bm: BigInt) = {
  require(a <= am)
  require(b <= bm)
  if a < b then {} else {}
} ensuring (max(a, b) <= max(am, bm))

def pow2(n: BigInt): BigInt = {
  require(n >= 0)
  if n == 0 then BigInt(1) else 2 * pow2(n - 1)
} ensuring (_ >= 1)

def pow2Max(a: BigInt, b: BigInt): Unit = {
  require(a >= 0 && b >= 0)
  decreases(a)
  if a == 0 || b == 0 then {} else
    assert(max(a, b) == 1 + max(a - 1, b - 1))
    pow2Max(a - 1, b - 1)
    assert(max(pow2(a), pow2(b)) == 2 * max(pow2(a - 1), pow2(b - 1)))
} ensuring (pow2(max(a, b)) == max(pow2(a), pow2(b)))

extension [T](n: Node[T]) {
  def climbUp(ds: List[Data[T]]): Unit = {
    require(
      ds.forall(d => n.left.query(d.key) == Some[T](d.value))
        || ds.forall(d => n.right.query(d.key) == Some[T](d.value))
    )
    ds match
      case Nil() => {}
      case Cons(h, t) => {
        if ds.forall(d => n.left.query(d.key) == Some[T](d.value)) then
          climbUp(h)
          climbUp(t)
        else
          climbUp(h)
          climbUp(t)
      }
  } ensuring (ds.forall(d => n.query(d.key) == Some[T](d.value)))
  def climbUp(d: Data[T]): Unit = {
    require(
      n.left.query(d.key) == Some[T](d.value)
        || n.right.query(d.key) == Some[T](d.value)
    )
    if n.left.query(d.key) == Some[T](d.value) then
      extractForAll(n.left, d.key, lessThan(_, n.indexedKey)) // lessThan(d.key, n.indexedKey)
      assert(n.contains(d.key) && n.get(d.key) == n.left.get(d.key))
    else
      extractForAll(n.right, d.key, greaterThan(_, n.indexedKey)) // greaterThan(d.key, n.indexedKey)
      rightContainsNotInLeft(n, d.key)
      assert(n.contains(d.key) && n.get(d.key) == n.right.get(d.key))
  } ensuring (n.query(d.key) == Some[T](d.value))
  def climbUpLt(ys: List[IndexedKey]): Unit = {
    require(n.left.forallKeys(k => ys.forall(lessThan(k, _))))
    require(n.right.forallKeys(k => ys.forall(lessThan(k, _))))
    require(ys.forall(lessThan(n.key, _)))
  } ensuring (n.forallKeys(k => ys.forall(lessThan(k, _))))
  def climbUpGt(ys: List[IndexedKey]): Unit = {
    require(n.left.forallKeys(k => ys.forall(greaterThan(k, _))))
    require(n.right.forallKeys(k => ys.forall(greaterThan(k, _))))
    require(ys.forall(greaterThan(n.key, _)))
  } ensuring (n.forallKeys(k => ys.forall(greaterThan(k, _))))
}

extension [T](t: Tree[T]) {
  def listExtractLt(y: IndexedKey, ys: List[IndexedKey]): Unit = {
    require(t.forallKeys(k => (y :: ys).forall(lessThan(k, _))))
    t match
      case Empty() => {}
      case Node(data, index, left, right) => {
        left.listExtractLt(y, ys)
        right.listExtractLt(y, ys)
      }
  } ensuring (t.forallKeys(lessThan(_, y))
    && t.forallKeys(k => ys.forall(lessThan(k, _))))
  def listExtractGt(y: IndexedKey, ys: List[IndexedKey]): Unit = {
    require(t.forallKeys(k => (y :: ys).forall(greaterThan(k, _))))
    t match
      case Empty() => {}
      case Node(data, index, left, right) => {
        left.listExtractGt(y, ys)
        right.listExtractGt(y, ys)
      }
  } ensuring (t.forallKeys(greaterThan(_, y))
    && t.forallKeys(k => ys.forall(greaterThan(k, _))))
}

extension [T](xs: List[Data[T]]) {
  def conditionListAppendLt(
      y: IndexedKey,
      ys: List[IndexedKey]
  ): Unit = {
    require(xs.forall(x => ys.forall(lessThan(x.key, _))))
    require(xs.forall(d => lessThan(d.key, y)))
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        assert((y :: ys).forall(lessThan(h.key, _)))
        t.conditionListAppendLt(y, ys)
  } ensuring (xs.forall(x => (y :: ys).forall(lessThan(x.key, _))))

  def conditionListAppendGt(
      y: IndexedKey,
      ys: List[IndexedKey]
  ): Unit = {
    require(xs.forall(x => ys.forall(greaterThan(x.key, _))))
    require(xs.forall(d => greaterThan(d.key, y)))
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        assert((y :: ys).forall(greaterThan(h.key, _)))
        t.conditionListAppendGt(y, ys)
  } ensuring (xs.forall(x => (y :: ys).forall(greaterThan(x.key, _))))
}

extension [T](xs: List[Data[T]]) {
  def isUnique: Boolean = xs match
    case Cons(h, t) => !t.containsKey(h.key) && t.isUnique
    case Nil()      => true

  def isSameSize: Boolean = xs match
    case Nil()          => true
    case Cons(h, Nil()) => true
    case Cons(h, t @ Cons(h2, _)) =>
      h.key.length == h2.key.length && t.isSameSize

  def isSameSizeAs(k: Key): Boolean = xs match
    case Nil()      => true
    case Cons(h, t) => h.key.length == k.length && t.isSameSizeAs(k)

  def containsKey(k: Key): Boolean = xs match
    case Cons(h, t) => h.key == k || t.containsKey(k)
    case Nil()      => false

  /** Given a ranking `k`, takes the `k`-th largest element, and split the
    * remaining arrays into "less than `k`" and "greater than `k`".
    */
  def kthElementByIndex(
      index: Index,
      k: BigInt
  ): (Data[T], List[Data[T]], List[Data[T]]) = {
    require(isSameSize)
    require(isUnique)
    require(xs.size > 0)
    require(0 <= k && k < xs.size)
    require(0 <= index && index < xs.head.key.length)
    val key = xs.head.key
    headSameIsSame(key)
    val (kth, less, greater) = kthElementByIndex(index, k, key)
    less.sameSizeAsEq(key, kth.key)
    greater.sameSizeAsEq(key, kth.key)
    kthElementByIndex(index, k, key)
  } ensuring ((kth, less, greater) =>
    // length conditions
    less.isSameSizeAs(kth.key) && greater.isSameSizeAs(kth.key)
      && less.isUnique && greater.isUnique
      // size conditions
      && less.size == k && greater.size == xs.size - k - 1
      // element conditions
      && xs.contains(kth)
      && less.forall(d => lessThan(d.key, IndexedKey(index, kth.key)))
      && greater.forall(d => greaterThan(d.key, IndexedKey(index, kth.key)))
      // sublist conditions
      && xs.containsList(less)
      && xs.containsList(greater)
      && tup(less, kth, greater).containsList(xs)
  )
  def kthElementByIndex(
      index: Index,
      k: BigInt,
      key: Key
  ): (Data[T], List[Data[T]], List[Data[T]]) = {
    require(isSameSizeAs(key))
    require(isUnique)
    require(xs.size > 0)
    require(0 <= k && k < xs.size)
    require(0 <= index && index < xs.head.key.length)
    decreases(xs.size)

    val Cons(h, t) = xs: @unchecked

    assert(h.key.length == key.length)
    t.sameSizeAsEq(key, h.key)

    val (lessThanH, moreThanH) =
      t.strongPartitionByOrder(index, h.key)
    lessThanH.sameSizeAsEq(h.key, key)
    moreThanH.sameSizeAsEq(h.key, key)
    xs.filterContains(d =>
      lessThan(d.key, IndexedKey(index, h.key))
    ) // lessThanH is sublist
    xs.filterContains(d =>
      greaterThan(d.key, IndexedKey(index, h.key))
    ) // moreThanH is sublist
    t.extendTupContains(lessThanH, h, moreThanH) // ltH ++ h ++ mtH contains xs

    if lessThanH.size == k then (h, lessThanH, moreThanH)
    else if lessThanH.size > k then
      val (kth, less, greater0) = lessThanH.kthElementByIndex(index, k, key)
      lessThanH.containsListExtractCond(
        greater0,
        d => lessThan(d.key, IndexedKey(index, h.key))
      ) // greater0.forall(< h.key)
      // prove they all greater than kth
      lessThanH.listExtractForAll(
        kth,
        d => lessThan(d.key, IndexedKey(index, h.key))
      ) // h > kth
      moreThanH.gtAssoc(index, h.key, kth.key) // moreThanH.forall(> kth)
      val greater = mergeParts(
        index,
        key,
        greater0,
        h,
        moreThanH,
        d => greaterThan(d.key, IndexedKey(index, kth.key))
      )
      xs.regroupLeftContains(less, kth, greater0, lessThanH, h, moreThanH)
      xs.containsListAssoc(lessThanH, less)
      xs.containsListAssoc(lessThanH, greater0)
      xs.containsListAppend(greater0, h :: moreThanH)
      (kth, less, greater)
    else
      val (kth, less0, greater) =
        moreThanH.kthElementByIndex(index, k - lessThanH.size - 1, key)
      moreThanH.containsListExtractCond(
        less0,
        d => greaterThan(d.key, IndexedKey(index, h.key))
      ) // less0.forall(> h.key)
      // prove they all less than kth
      moreThanH.listExtractForAll(
        kth,
        d => greaterThan(d.key, IndexedKey(index, h.key))
      ) // h < kth
      lessThanH.ltAssoc(index, h.key, kth.key) // lessThanH.forall(< kth)
      val less = mergeParts(
        index,
        key,
        lessThanH,
        h,
        less0,
        d => lessThan(d.key, IndexedKey(index, kth.key))
      )
      xs.regroupRightContains(less0, kth, greater, lessThanH, h, moreThanH)
      xs.containsListAssoc(moreThanH, less0)
      xs.containsListAssoc(moreThanH, greater)
      xs.containsListAppend(lessThanH, h :: less0)
      (kth, less, greater)

  } ensuring ((kth, less, greater) =>
    kth.key.length == key.length
    // length conditions
      && less.isSameSizeAs(key) && greater.isSameSizeAs(key)
      && less.isUnique && greater.isUnique
      // size conditions
      && less.size == k && greater.size == xs.size - k - 1
      // element conditions
      && xs.contains(kth)
      && less.forall(d => lessThan(d.key, IndexedKey(index, kth.key)))
      && greater.forall(d => greaterThan(d.key, IndexedKey(index, kth.key)))
      // sublist conditions
      && xs.containsList(less)
      && xs.containsList(greater)
      && tup(less, kth, greater).containsList(xs)
  )

  def strongPartitionByOrder(
      index: BigInt,
      key: Key
  ): (List[Data[T]], List[Data[T]]) = {
    require(0 <= index && index < key.length)
    require(isUnique)
    require(isSameSizeAs(key))
    require(!containsKey(key))
    strongPartitionPreservesUnique(d => lessThan(d.key, IndexedKey(index, key)))
    strongPartitionPreservesSameSizeAs(
      key,
      d => lessThan(d.key, IndexedKey(index, key))
    )
    strongPartitionPreservesNotContains(
      key,
      d => lessThan(d.key, IndexedKey(index, key))
    )
    filterNotLessThan(index, key)
    xs.partitionContainsList(d => lessThan(d.key, IndexedKey(index, key)))
    val x = xs.strongPartition(d => lessThan(d.key, IndexedKey(index, key)))._2
    x.antisymm(index, key)

    xs.strongPartition(d => lessThan(d.key, IndexedKey(index, key)))

  } ensuring ((l, r) =>
    l.isUnique && r.isUnique
      && l.isSameSizeAs(key) && r.isSameSizeAs(key)
      && !l.containsKey(key) && !r.containsKey(key)
      && l.length + r.length == xs.length
      && l.forall(d => lessThan(d.key, IndexedKey(index, key)))
      && r.forall(d => greaterThan(d.key, IndexedKey(index, key)))
      && (l ++ r).containsList(xs)
  )

  def filterNotLessThan(index: BigInt, key: Key): Unit = {
    require(0 <= index && index < key.length)
    require(isSameSizeAs(key))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        if lessThan(h.key, IndexedKey(index, key)) then
          // it's not in result
          t.filterNotLessThan(index, key)
        else t.filterNotLessThan(index, key)
      }
  } ensuring (xs
    .filterNot(d => lessThan(d.key, IndexedKey(index, key)))
    .forall(d => !lessThan(d.key, IndexedKey(index, key))))

  def sameSizeAsEq(k1: Key, k2: Key): Unit = {
    require(isSameSizeAs(k1))
    require(k1.length == k2.length)
    xs match
      case Nil()      => {}
      case Cons(h, t) => t.sameSizeAsEq(k1, k2)
  } ensuring (isSameSizeAs(k2))

  def antisymm(index: BigInt, key: Key): Unit = {
    require(0 <= index && index < key.length)
    require(isSameSizeAs(key))
    require(xs.forall(d => !lessThan(d.key, IndexedKey(index, key))))
    require(!containsKey(key))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        assert(h.key != key)
        assert(h.key.length == key.length)
        val comp = keyOrderBy(index, h.key, key)
        keyOrderByEq(index, h.key, key)
        keyOrderByAntisym(index, h.key, key)
        t.antisymm(index, key)
      }
  } ensuring (xs.forall(d => greaterThan(d.key, IndexedKey(index, key))))

  def sameAsIsSame(k: Key): Unit = {
    require(xs.isSameSizeAs(k))
    xs match
      case Nil()          => {}
      case Cons(h, Nil()) => {}
      case Cons(h, t @ Cons(h2, _)) =>
        assert(h2.key.length == k.length)
        t.sameAsIsSame(k)
  } ensuring (xs.isSameSize)

  def headSameIsSame(k: Key): Unit = {
    require(xs.size > 0)
    require(xs.head.key.length == k.length)
    require(xs.isSameSize)
    xs match
      case Nil()          => {}
      case Cons(h, Nil()) => {}
      case Cons(h, t @ Cons(h2, _)) =>
        assert(h2.key.length == k.length)
        t.headSameIsSame(k)
  } ensuring (xs.isSameSizeAs(k))

  def strongPartitionPreservesSameSize(
      cond: Data[T] => Boolean
  ): Unit = {
    require(isSameSize)
    xs match
      case Nil() => {}
      case Cons(h, _) => {
        headSameIsSame(h.key)
        strongPartitionPreservesSameSizeAs(h.key, cond)
        val (l, r) = xs.strongPartition(cond)
        l.sameAsIsSame(h.key)
        r.sameAsIsSame(h.key)
      }
  } ensuring (_ =>
    val (l, r) = xs.strongPartition(cond)
    l.isSameSize && r.isSameSize
  )

  def strongPartitionPreservesSameSizeAs(
      key: Key,
      cond: Data[T] => Boolean
  ): Unit = {
    require(isSameSizeAs(key))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        assert(h.key.length == key.length)
        t.strongPartitionPreservesSameSizeAs(key, cond)
        val (l, r) = t.strongPartition(cond)
        assert((h :: l).isSameSizeAs(key))
        assert((h :: r).isSameSizeAs(key))
      }
  } ensuring (_ =>
    val (l, r) = xs.strongPartition(cond)
    l.isSameSizeAs(key) && r.isSameSizeAs(key)
  )

  def strongPartitionPreservesNotContains(
      v: Key,
      cond: Data[T] => Boolean
  ): Unit = {
    require(!containsKey(v))
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        val (l, r) = t.strongPartition(cond)
        t.strongPartitionPreservesNotContains(v, cond)
        assert(!(h :: l).containsKey(v))
        assert(!(h :: r).containsKey(v))
  } ensuring (_ =>
    val (l, r) = xs.strongPartition(cond)
    !l.containsKey(v) && !r.containsKey(v)
  )

  def strongPartitionPreservesUnique(cond: Data[T] => Boolean): Unit = {
    require(isUnique)
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        assert(!t.containsKey(h.key))
        val (tl, tr) = t.strongPartition(cond)
        t.strongPartitionPreservesUnique(cond)
        t.strongPartitionPreservesNotContains(h.key, cond)
        assert((h :: tl).isUnique)
        assert((h :: tr).isUnique)
      }
  } ensuring (_ =>
    val (l, r) = xs.strongPartition(cond)
    l.isUnique && r.isUnique
  )

  def gtIsNotContains(index: BigInt, key: Key): Unit = {
    require(0 <= index && index < key.length)
    require(xs.forall(d => greaterThan(d.key, IndexedKey(index, key))))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        keyOrderByEq(index, key, h.key)
        t.gtIsNotContains(index, key)
      }
  } ensuring (!xs.containsKey(key))

  def gtAssoc(index: BigInt, k1: Key, k2: Key): Unit = {
    require(0 <= index && index < k2.length)
    require(greaterThan(k1, IndexedKey(index, k2)))
    require(xs.forall(d => greaterThan(d.key, IndexedKey(index, k1))))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        keyOrderByAssoc(index, k2, k1, h.key)
        t.gtAssoc(index, k1, k2)
      }
  } ensuring (xs.forall(d => greaterThan(d.key, IndexedKey(index, k2))))

  def ltAssoc(index: BigInt, k1: Key, k2: Key): Unit = {
    require(0 <= index && index < k2.length)
    require(lessThan(k1, IndexedKey(index, k2)))
    require(xs.forall(d => lessThan(d.key, IndexedKey(index, k1))))
    xs match
      case Nil() => {}
      case Cons(h, t) => {
        keyOrderByAssoc(index, h.key, k1, k2)
        t.ltAssoc(index, k1, k2)
      }
  } ensuring (xs.forall(d => lessThan(d.key, IndexedKey(index, k2))))
}

def mergeParts[T](
    index: BigInt,
    key: Key,
    less: List[Data[T]],
    mid: Data[T],
    greater: List[Data[T]],
    cond: Data[T] => Boolean
): List[Data[T]] = {
  require(0 <= index && index < key.length)
  require(less.isSameSizeAs(key))
  require(mid.key.length == key.length)
  require(greater.isSameSizeAs(key))

  require(less.forall(cond))
  require(cond(mid))
  require(greater.forall(cond))

  require(less.isUnique)
  require(greater.isUnique)
  require(less.forall(d => lessThan(d.key, IndexedKey(index, mid.key))))
  require(greater.forall(d => greaterThan(d.key, IndexedKey(index, mid.key))))

  less match
    case Nil() =>
      greater.gtIsNotContains(index, mid.key)
      mid :: greater
    case Cons(h, t) =>
      val tail = mergeParts(index, key, t, mid, greater, cond)
      keyOrderByEq(index, h.key, mid.key) // h != mid
      greater.gtAssoc(index, mid.key, h.key) // greater.forall(> h)
      greater.gtIsNotContains(index, h.key) // h not in greater
      notContainsAppend(h.key, t, mid :: greater)
      h :: tail

} ensuring (r =>
  r == less ++ (mid :: greater)
    && r.isSameSizeAs(key)
    && r.forall(cond)
    && r.isUnique
)

def notContainsAppend[T](
    key: Key,
    l1: List[Data[T]],
    l2: List[Data[T]]
): Unit = {
  require(!l1.containsKey(key))
  require(!l2.containsKey(key))
  l1 match
    case Nil() => {}
    case Cons(h, t) => {
      assert(l1 ++ l2 == h :: (t ++ l2))
      notContainsAppend(key, t, l2)
    }
} ensuring (!(l1 ++ l2).containsKey(key))

inline def tup[T](as: List[T], b: T, cs: List[T]) = as ++ (b :: cs)

def openTup[T](as: List[T], b: T, cs: List[T], v: T): Unit = {
  require(tup(as, b, cs).contains(v))
  as match
    case Nil()      => if b == v then {} else {}
    case Cons(h, t) => if h == v then {} else openTup(t, b, cs, v)
} ensuring (as.contains(v) || b == v || cs.contains(v))

def openTupR[T](as: List[T], b: T, cs: List[T], v: T): Unit = {
  require(as.contains(v) || b == v || cs.contains(v))
  if as.contains(v) then
    as match
      case Cons(h, t) => if h == v then {} else openTupR(t, b, cs, v)
      case Nil()      => {}
  else
    as match
      case Cons(_, t) => openTupR(t, b, cs, v)
      case Nil()      => if b == v then {} else {}
} ensuring (tup(as, b, cs).contains(v))

def tupCond[T](as: List[T], b: T, cs: List[T], cond: T => Boolean): Unit = {
  require(as.forall(cond))
  require(cond(b))
  require(cs.forall(cond))
  as match
    case Cons(_, t) => tupCond(t, b, cs, cond)
    case Nil()      => {}
} ensuring (tup(as, b, cs).forall(cond))
