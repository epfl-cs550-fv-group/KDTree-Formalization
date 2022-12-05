import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

// object Tree {
//   def optimalConstruct[T](
//       arr: Map[Key, T],
//       ub: List[IndexedKey],
//       lb: List[IndexedKey]
//   ): Tree[T] = {
//     require(ub.forall(ik => arr.keys.forall(lessThan(_, IndexedKey(ik)))))
//     require(lb.forall(ik => arr.keys.forall(greaterThan(_, IndexedKey(ik)))))
//     val keys = arr.keys
//     keys match
//       case Nil()         => Empty()
//       case keys: Cons[T] => ???

//   } ensuring (r =>
//     // size conditions
//     r.size == arr.keys.size
//     // bound conditions
//       && ub.forall(ik => r.forallKeys(lessThan(_, IndexedKey(ik))))
//       && lb.forall(ik => r.forallKeys(greaterThan(_, IndexedKey(ik))))
//   )
// }

extension [T](xs: List[T]) {
  def containsList(ys: List[T]): Boolean = ys match
    case Cons(h, t) => xs.contains(h) && xs.containsList(t)
    case Nil()      => true

  def filterContains(cond: T => Boolean): Unit = {
    def containsListAppend[A](x: A, l1: List[A], l2: List[A]): Unit = {
      require(l1.containsList(l2))
      l2 match
        case Cons(h, t) => containsListAppend(x, l1, t)
        case Nil()      => {}
    } ensuring ((x :: l1).containsList(l2))
    xs match
      case Cons(h, t) => {
        if cond(h) then
          assert(xs.filter(cond) == h :: t.filter(cond))
          assert(xs.filterNot(cond) == t.filterNot(cond))
          t.filterContains(cond)
          containsListAppend(h, t, t.filter(cond))
          containsListAppend(h, t, t.filterNot(cond))
        else
          assert(xs.filter(cond) == t.filter(cond))
          assert(xs.filterNot(cond) == h :: t.filterNot(cond))
          t.filterContains(cond)
          containsListAppend(h, t, t.filter(cond))
          containsListAppend(h, t, t.filterNot(cond))
      }
      case Nil() => {}
  } ensuring (
    xs.containsList(xs.filter(cond))
      && xs.containsList(xs.filterNot(cond))
  )

  def containsListExtractCond(ys: List[T], cond: T => Boolean): Unit = {
    require(xs.containsList(ys))
    require(xs.forall(cond))
    ys match
      case Cons(h, t) =>
        xs.listExtractForAll(h, cond)
        containsListExtractCond(t, cond)
      case Nil() => {}
  } ensuring (ys.forall(cond))

  def containsListAppend(l1: List[T], l2: List[T]): Unit = {
    require(containsList(l1))
    require(containsList(l2))
    l1 match
      case Cons(h, t) => containsListAppend(t, l2)
      case Nil()      => {}
  } ensuring (containsList(l1 ++ l2))

  def containsListAssoc(l1: List[T], l2: List[T]): Unit = {
    require(containsList(l1))
    require(l1.containsList(l2))
    def oneElem(l1: List[T], x: T): Unit = {
      require(containsList(l1))
      require(l1.contains(x))
      l1 match
        case Cons(h, t) => if h == x then {} else oneElem(t, x)
        case Nil()      => {}
    } ensuring (xs.contains(x))
    l2 match
      case Cons(h, t) =>
        oneElem(l1, h)
        containsListAssoc(l1, t)
      case Nil() => {}
  } ensuring (containsList(l2))

  def listExtractForAll(elem: T, cond: T => Boolean): Unit = {
    require(xs.forall(cond))
    require(xs.contains(elem))
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        if h != elem then t.listExtractForAll(elem, cond)
  } ensuring (cond(elem))
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
