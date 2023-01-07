import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

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

  def extendTupContains(l: List[T], x: T, r: List[T]): Unit = {
    require((l ++ r).containsList(xs))
    def containsAppendX(l: List[T]): Unit = {
      l match
        case Cons(h, t) => if h == x then {} else containsAppendX(t)
        case Nil()      => {}
    } ensuring ((l ++ (x :: r)).contains(x))
    def containsOneOf(l: List[T], v: T): Unit = {
      require((l ++ r).contains(v))
      l match
        case Cons(h, t) => if h == v then {} else containsOneOf(t, v)
        case Nil()      => {}
    } ensuring (l.contains(v) || r.contains(v))
    def containsOneOfR(l: List[T], r: List[T], v: T): Unit = {
      require(l.contains(v) || r.contains(v))
      l match
        case Nil()      => {}
        case Cons(h, t) => if h == v then {} else containsOneOfR(t, r, v)
    } ensuring ((l ++ r).contains(v))
    def containsAppendXs(xs: List[T]): Unit = {
      require((l ++ r).containsList(xs))
      xs match
        case Cons(h, t) =>
          containsOneOf(l, h)
          if l.contains(h) then containsOneOfR(l, x :: r, h)
          else containsOneOfR(l, x :: r, h)
          containsAppendXs(t)
        case Nil() => {}
    } ensuring ((l ++ (x :: r)).containsList(xs))
    containsAppendX(l)
    containsAppendXs(xs)
  } ensuring ((l ++ (x :: r)).containsList(x :: xs))

  def extendTupContains(x: T, l: List[T], r: List[T]): Unit = {
    require((l ++ r).containsList(xs))
    def recurse(xs: List[T]): Unit = {
      require((l ++ r).containsList(xs))
      xs match
        case Nil() => {}
        case Cons(h, t) =>
          assert((x :: (l ++ r)).contains(h))
          recurse(t)
    } ensuring (((x :: l) ++ r).containsList(xs))
    recurse(xs)
  } ensuring (((x :: l) ++ r).containsList(x :: xs))

  def regroupLeftContains(
      as: List[T],
      b: T,
      cs: List[T],
      ds: List[T],
      e: T,
      fs: List[T]
  ): Unit = {
    require(tup(as, b, cs).containsList(ds))
    require(tup(ds, e, fs).containsList(xs))
    xs match
      case Nil() => {}
      case Cons(v, t) =>
        t.regroupLeftContains(as, b, cs, ds, e, fs)
        openTup(ds, e, fs, v)
        if ds.contains(v) then
          tup(as, b, cs).containsListAssocElem(ds, v)
          openTup(as, b, cs, v)
          if cs.contains(v) then openTupR(cs, e, fs, v)
          openTupR(as, b, tup(cs, e, fs), v)
        else
          openTupR(cs, e, fs, v)
          openTupR(as, b, tup(cs, e, fs), v)
  } ensuring (tup(as, b, tup(cs, e, fs)).containsList(xs))

  def regroupRightContains(
      as: List[T],
      b: T,
      cs: List[T],
      ds: List[T],
      e: T,
      fs: List[T]
  ): Unit = {
    require(tup(as, b, cs).containsList(fs))
    require(tup(ds, e, fs).containsList(xs))
    xs match
      case Nil() => {}
      case Cons(v, t) =>
        t.regroupRightContains(as, b, cs, ds, e, fs)
        openTup(ds, e, fs, v)
        if fs.contains(v) then
          tup(as, b, cs).containsListAssocElem(fs, v)
          openTup(as, b, cs, v)
          if as.contains(v) then openTupR(ds, e, as, v)
          openTupR(tup(ds, e, as), b, cs, v)
        else
          openTupR(ds, e, as, v)
          openTupR(tup(ds, e, as), b, cs, v)
  } ensuring (tup(tup(ds, e, as), b, cs).containsList(xs))

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

  def partitionContainsList(cond: T => Boolean): Unit = {
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        t.partitionContainsList(cond)
        val (tl, tr) = t.strongPartition(cond)
        if cond(h) then {
          t.extendTupContains(h, tl, tr)
        } else {
          t.extendTupContains(tl, h, tr)
        }
  } ensuring ({
    val (l, r) = xs.strongPartition(cond)
    (l ++ r).containsList(xs)
  })

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

  def containsListAssocElem(l1: List[T], v: T): Unit = {
    require(containsList(l1))
    require(l1.contains(v))
    containsListAssoc(l1, List(v))
  } ensuring (xs.contains(v))

  def listExtractForAll(elem: T, cond: T => Boolean): Unit = {
    require(xs.forall(cond))
    require(xs.contains(elem))
    xs match
      case Nil() => {}
      case Cons(h, t) =>
        if h != elem then t.listExtractForAll(elem, cond)
  } ensuring (cond(elem))

  def listContentConcatCond(l1: List[T], l2: List[T], cond: T => Boolean): Unit = {
    require(xs.forall(elem => l1.contains(elem) || l2.contains(elem)))
    require(l1.forall(cond))
    require(l2.forall(cond))
    xs match {
      case Nil() => 
      case Cons(h, t) => 
        assert(l1.contains(h) || l2.contains(h))
        if l1.contains(h) then 
          l1.listExtractForAll(h, cond)
        else 
          l2.listExtractForAll(h, cond)
        t.listContentConcatCond(l1, l2, cond) // t.forall(cond)
    }
  } ensuring (xs.forall(cond))
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
