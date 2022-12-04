import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

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
