import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod

extension [T](tree: Tree[T]){
	
  def insertWithRotatingIndex(data: Data[T], from: BigInt): Node[T] = {
    require(0 <= from && from < data.key.length)
    require(tree.compatible(data))
    tree.insertWithRotatingIndex(data, from, List(), List())
  } ensuring (r =>
    // membership condition
      r.containsData(data)
      // size condition
      && tree.size <= r.size && r.size <= tree.size + 1
      // consistency condition
      && equalExcept(tree, r, data.key)
  )

  def insertWithRotatingIndex(
      data: Data[T],
      from: BigInt,
      ub: List[IndexedKey],
      lb: List[IndexedKey]
  ): Node[T] = {
    require(0 <= from && from < data.key.length)
    require(tree.compatible(data))
    require(ub.forall(lessThan(data.key, _)))
    require(ub.forall(ik => tree.forallKeys(k1 => lessThan(k1, ik))))
    require(lb.forall(greaterThan(data.key, _)))
    require(lb.forall(ik => tree.forallKeys(k1 => greaterThan(k1, ik))))

    tree match {
      case Empty() =>
        val r = Node(data, from, Empty(), Empty())
        listLtNode(ub, r)
        listGtNode(lb, r)
        assert(equalExcept(tree, r, data.key))
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
          rootContainsRightData(r, data)
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
      r.containsData(data)
      // size condition
      && tree.size <= r.size && r.size <= tree.size + 1
      // bound conditions
      && ub.forall(ik => r.forallKeys(k1 => lessThan(k1, ik)))
      && lb.forall(ik => r.forallKeys(k1 => greaterThan(k1, ik)))
      // consistency condition
      && equalExcept(tree, r, data.key)
  )

  /** Erases a key from the tree. Returns the old tree if the key does not
    * exist.
    */
  def erase(key: Key): Tree[T] = {
    if tree.contains(key) then tree.erase(key, List(), List(), List())
    else 
      equalExceptSelf(tree, key)
      tree
  } ensuring (r =>
    // membership condition
    !r.contains(key)
    // size condition
      && tree.size - 1 <= r.size && r.size <= tree.size
      // consistency condition
      && equalExcept(tree, r, key)
  )

  /** Erases a key from the tree. The key must exist inside the tree. */
  def erase(
      key: Key,
      ub: List[IndexedKey],
      ueb: List[IndexedKey],
      lb: List[IndexedKey]
  ): Tree[T] = {
    require(tree.contains(key))
    require(ub.forall(ik => tree.forallKeys(k1 => lessThan(k1, ik))))
    require(ueb.forall(ik => tree.forallKeys(k1 => lessThanEq(k1, ik))))
    require(lb.forall(ik => tree.forallKeys(k1 => greaterThan(k1, ik))))
    decreases(tree.size)
    tree match
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
          equalExceptInferFromLeft(n, r, key)
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
          equalExceptInferFromRight(n, r, key)
          r
        else
          keyOrderByEq(index, key, d.key) // key != d.key
          assert(right.forallKeys(greaterThan(_, ik)))
          assert(!greaterThan(key, ik))
          extractNotContains(right, key, k => greaterThan(k, ik))
          left match {
            case Empty()    => 
              equalExceptInferFromRightErased(n, right, key)
              right
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
              equalExceptInferFromLeftErased(n, r, greatestLeft.key, key)
              r
          }
  } ensuring (r =>
    // membership condition
    !r.contains(key)
    // size condition
      && tree.size - 1 == r.size
      // bound conditions
      && ub.forall(ik => r.forallKeys(k1 => lessThan(k1, ik)))
      && ueb.forall(ik => r.forallKeys(k1 => lessThanEq(k1, ik)))
      && lb.forall(ik => r.forallKeys(k1 => greaterThan(k1, ik)))
      // consistency condition
      && equalExcept(tree, r, key)
  )
}


// Start of equalExcept condition definition and lemmas. 

def equalCond[T](a: Tree[T], b: Tree[T], key: Key): Boolean = 
  a.query(key) == b.query(key)

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

def equalExceptSelf[T](t: Tree[T], excKey: Key): Unit = {
  def recur(ls: List[Key]): Unit = {
    ls match {
      case Nil() => 
      case Cons(head, tail) => 
        assert(equalExceptCond(t, t, excKey, head))
        recur(tail)
    }
  } ensuring (ls.forall(k => equalExceptCond(t, t, excKey, k)))
  recur(t.keys)
} ensuring(equalExcept(t, t, excKey))

// End of equalExcept condition definition and lemmas. 

def rootContainsChildKeys[T](t: Node[T], ks: List[Key]): Unit = {
  require(ks.forall(t.left.contains) || ks.forall(t.right.contains))

  ks match {
    case Nil() => 
    case Cons(head, tail) => 
      assert(t.left.contains(head) || t.right.contains(head))
      assert(tail.forall(t.left.contains) || tail.forall(t.right.contains))
      assert(t.contains(head))
      rootContainsChildKeys(t, tail)
  }
} ensuring (ks.forall(t.contains))

def neqNotContainsRootKey[T](t: Tree[T], ik: IndexedKey): Unit = {
  require(t.forallKeys(k => lessThan(k, ik)) || t.forallKeys(k => greaterThan(k, ik)))
  t match {
    case Empty() => 
    case Node(data, index, left, right) => 
      assert(lessThan(data.key, ik) || greaterThan(data.key, ik))
      assert(data.key != ik.key)
      neqNotContainsRootKey(left, ik)
      neqNotContainsRootKey(right, ik)
  }
} ensuring (!t.contains(ik.key))

def forallNeq[T](t: Tree[T], ik: IndexedKey): Unit = {
  require(t.forallKeys(k => lessThan(k, ik)) || t.forallKeys(k => greaterThan(k, ik)))
  t match {
    case Empty() => 
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
  rootContainsChildKeys(a, ks) // ks.forall(a.contains)
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
  rootContainsChildKeys(a, ks) // ks.forall(a.contains)
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

def equalExceptCondChangeKey[T](a: Tree[T], b: Tree[T], k0: Key, k1: Key, ks: List[Key]): Unit = {
  require(ks.forall(k => equalExceptCond(a, b, k0, k)))
  require(!ks.contains(k0) && !ks.contains(k1))

  ks match {
    case Nil() => 
    case Cons(h, t) => 
      assert(h != k0 && h != k1)
      assert(equalExceptCond(a, b, k0, h))
      assert(a.query(h) == b.query(h))
      assert(equalExceptCond(a, b, k1, h))
      equalExceptCondChangeKey(a, b, k0, k1, t)
  }
} ensuring (ks.forall(k => equalExceptCond(a, b, k1, k)))

def listAppendContains[T](l0: List[T], l1: List[T], elem: T): List[T] = {
  require(l0.contains(elem))
  l0 match {
    case Nil() => assert(false)
    case Cons(h, t) => 
      assert(h == elem || t.contains(elem))
      if h == elem then 
        assert((l0 ++ l1).contains(elem))  // l0 ++ l1 == h :: (t ++ l1)
      else 
        assert(t.contains(elem))
        listAppendContains(t, l1, elem)
        assert((l0 ++ l1).contains(elem))
  }
  l0 ++ l1
} ensuring (r => r.contains(elem))

def listPrependContains[T](l0: List[T], l1: List[T], elem: T): List[T] = {
  require(l1.contains(elem))
  l0 match {
    case Nil() => assert(l0 ++ l1 == l1)
    case Cons(h, t) =>
      listPrependContains(t, l1, elem) // (t ++ l1).contains(elem)
      assert((l0 ++ l1).contains(elem))
  }
  l0 ++ l1
} ensuring (r => r.contains(elem))

def keysContains[T](t: Tree[T], key: Key): Unit = {
  require(t.contains(key))
  t match {
    case Empty() =>
    case Node(data, index, left, right) => 
      assert(data.key == key || left.contains(key) || right.contains(key))
      if data.key == key then 
        assert(List(data.key).contains(key))
        val v0 = listAppendContains(List(data.key), left.keys, key)
        val v1 = listAppendContains(v0, right.keys, key)
        assert(v1 == t.keys)
      else if left.contains(key) then 
        keysContains(left, key) // left.keys.contains(key)
        val v0 = listPrependContains(List(data.key), left.keys, key)
        val v1 = listAppendContains(v0, right.keys, key)
        assert(v1 == t.keys)
      else 
        assert(right.contains(key))
        keysContains(right, key) // right.keys.contains(key)
        val v0 = listPrependContains(left.keys, right.keys, key)
        val v1 = listPrependContains(List(data.key), v0, key)
        assert(v1 == t.keys)
  }
} ensuring (t.keys.contains(key))

def keysContainsNeg[T](t: Tree[T], key: Key): Unit = {
  require(!t.contains(key))
  t match {
    case Empty() =>
    case Node(data, index, left, right) => 
      assert(data.key != key && !left.contains(key) && !right.contains(key))
      keysContainsNeg(left, key)
      keysContainsNeg(right, key)
  }
} ensuring (!t.keys.contains(key))

def equalExceptToContains[T](a: Tree[T], b: Tree[T], excKey: Key, ks: List[Key], xs: List[Key], ys: List[Key]): Unit = {
  require(ks.forall(k => equalExceptCond(a, b, excKey, k)))
  require(ks.forall(a.contains))
  require(xs == b.keys)
  require(ys == List(excKey))
  ks match {
    case Nil() => 
    case Cons(h, t) => 
      assert(equalExceptCond(a, b, excKey, h))
      assert(a.contains(h))
      if h != excKey then 
        assert(a.query(h) == b.query(h))
        assert(a.get(h) == b.get(h))
        assert(b.contains(h))
        keysContains(b, h)
        assert(b.keys.contains(h))
        assert(xs.contains(h))
      else 
        assert(List(excKey).contains(h))
        assert(ys.contains(h))
      // assert(b.keys.contains(h) || List(excKey).contains(h))
      assert(xs.contains(h) || ys.contains(h))
      equalExceptToContains(a, b, excKey, t, xs, ys)
  }
} ensuring (ks.forall(k => xs.contains(k) || ys.contains(k)))

def raiseEqualExceptCondSelfRight[T](a: Node[T], excKey: Key, ks: List[Key]): Unit = {
  require(ks.forall(a.right.contains))
  rootContainsChildKeys(a, ks) // ks.forall(a.contains)
  equalExceptReflect(a.right, excKey, ks) // ks.forall(k => equalExceptCond(a.right, a.right, excKey, k))
  ks match {
    case Nil() => 
    case Cons(h, t) => 
      assert(equalExceptCond(a.right, a.right, excKey, h))
      assert(a.contains(h))
      if h != excKey then {
        assert(a.right.get(h) == a.right.get(h))
        rightGetToRootGet(a, h) // a.get(h) == a.right.get(h)
        assert(equalExceptCond(a, a.right, excKey, h))
      }
      assert(equalExceptCond(a, a.right, excKey, h))
      raiseEqualExceptCondSelfRight(a, excKey, t)
  }
} ensuring (ks.forall(k => equalExceptCond(a, a.right, excKey, k)))

def equalExceptInferFromRightErased[T](a: Node[T], b: Tree[T], excKey: Key): Unit = {
  require(a.right == b)
  require(a.left.keys.isEmpty)
  require(a.data.key == excKey)

  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  raiseEqualExceptCondSelfRight(a, excKey, a.right.keys)
  assert(a.right.keys.forall(cond))

  assert(cond(excKey))
  assert(a.keys == List(excKey) ++ a.right.keys)
  listConcatCond(List(excKey), a.right.keys, cond)
  assert(!a.keys.isEmpty && a.keys.forall(cond))
} ensuring (equalExcept(a, b, excKey))

def equalExceptInferFromLeftErased[T](a: Node[T], b: Node[T], rootKey: Key, excKey: Key): Unit = {
  // left preconds
  require(equalExcept(a.left, b.left, rootKey))
  require(a.left.contains(rootKey) && a.left.get(rootKey) == b.data.value)
  // right preconds
  require(a.right == b.right)
  // root preconds
  require(a.data.key == excKey)
  require(b.data.key == rootKey)
  require(!b.contains(excKey))
  
  val cond = (k: Key) => equalExceptCond(a, b, excKey, k)
  // a.right, b.right
  equalExceptReflect(a.right, excKey, a.right.keys) 
  equalExceptReflect(b.right, excKey, b.right.keys) 
  raiseEqualExceptCondFromRight(a, b, excKey)
  assert(a.right.keys.forall(cond) && b.right.keys.forall(cond))
  // b.left
  raiseEqualExceptCondFromLeft(a, b, rootKey) 
  neqNotContainsRootKey(b.left, IndexedKey(b.index, b.data.key)) // !b.left.contains(b.data.key)
  keysContainsNeg(b.left, excKey)
  keysContainsNeg(b.left, rootKey)
  equalExceptCondChangeKey(a, b, rootKey, excKey, b.left.keys) // b.left.keys.forall(k => equalExceptCond(a, b, excKey, k))
  assert(b.left.keys.forall(cond))
  // b.root
  leftGetToRootGet(a, rootKey) // a.contains(key) && a.get(key) == a.left.get(key)
  assert(b.contains(rootKey) && b.get(rootKey) == b.data.value)
  assert(a.get(rootKey) == b.get(rootKey))
  assert(cond(rootKey))
  // b
  listConcatCond3(List(rootKey), b.left.keys, b.right.keys, cond)
  assert(!b.keys.isEmpty && b.keys.forall(cond))
  // a.left: a.left.content == b.left.content ++ Set(rootKey)
  equalExceptToContains(a.left, b.left, rootKey, a.left.keys, b.left.keys, List(rootKey))
  a.left.keys.listContentConcatCond(b.left.keys, List(rootKey), cond)
  assert(a.left.keys.forall(cond))
  // a.root
  assert(cond(excKey))
  // a
  listConcatCond3(List(excKey), a.left.keys, a.right.keys, cond)
  assert(!a.keys.isEmpty && a.keys.forall(cond))
  // conclusion
  assert(equalExcept(a, b, excKey))
} ensuring(equalExcept(a, b, excKey))