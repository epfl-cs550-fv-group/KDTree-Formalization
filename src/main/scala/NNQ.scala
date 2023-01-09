import stainless.lang._
import stainless.collection._

object NNQ {
  def abs(x: BigInt, y: BigInt): BigInt = {
    val res = x - y
    if res < 0 then -res else res
  } ensuring { res => res >= 0 }

  def l1Dist(p1: Key, p2: Key): BigInt = {
    require(p1.length == p2.length)
    (p1, p2) match {
      case (Nil(), Nil()) => (0: BigInt)
      case (Cons(x, xs), Cons(y, ys)) =>
        val l = abs(x, y)
        val rem = l1Dist(xs, ys)
        l + rem
    }
  } ensuring { res => res >= 0 }

  def l1DistLowerBound(p1: Key, p2: Key, k: BigInt, d: BigInt): Unit = {
    require(p1.length == p2.length)
    require(0 <= k && k < p1.length)
    require(d >= 0)
    require(abs(p1(k), p2(k)) >= d)

    (p1, p2) match {
      case (Nil(), Nil()) => ()
      case (Cons(x, xs), Cons(y, ys)) =>
        if k == 0 then
          ()
        else
          l1DistLowerBound(xs, ys, k - 1, d)
    }
  } ensuring {
    l1Dist(p1, p2) >= d
  }

  def isCompatibleData[T](x: Key, xs: List[Data[T]]): Boolean =
    xs match {
      case Nil() => true
      case Cons(y, ys) => x.length == y.key.length && isCompatibleData(x, ys)
    }

  def membership[T](res: List[Data[T]], tree: Tree[T], acc: List[Data[T]]): Boolean =
    res.forall { data => tree.contains(data.key) || acc.contains(data) }

  def findMaxElem[T](p: Key, ps: List[Data[T]]): (BigInt, Data[T], List[Data[T]]) = {
    require(ps.length > 0)
    require(isCompatibleData(p, ps))

    ps match {
      case Cons(q, Nil()) => (l1Dist(p, q.key), q, Nil())
      case Cons(q, qs) =>
        val dq = l1Dist(p, q.key)
        val (dq1, q1, qs1) = findMaxElem(p, qs)
        if dq > dq1 then
          (dq, q, qs)
        else
          (dq1, q1, q :: qs1)
    }
  } ensuring { (dx, x, xs) =>
    dx == l1Dist(p, x.key) &&
      xs.length == ps.length - 1 &&
      isCompatibleData(p, xs)
  }

  def isUpperBoundDist[T](d: BigInt, p: Key, ps: List[Data[T]]): Boolean = {
    require(isCompatibleData(p, ps))
    ps match
      case Cons(q, qs) => d >= l1Dist(p, q.key) && isUpperBoundDist(d, p, qs)
      case Nil() => true
  }

  def relaxUpperBound[T](d1: BigInt, d2: BigInt, p: Key, ps: List[Data[T]]): Unit = {
    require(isCompatibleData(p, ps))
    require(isUpperBoundDist(d1, p, ps))
    require(d1 <= d2)

    ps match {
      case Nil() => ()
      case Cons(q, ps) =>
        relaxUpperBound(d1, d2, p, ps)
    }

  } ensuring {
    isUpperBoundDist(d2, p, ps)
  }

  def foundMaxElem[T](p: Key, ps: List[Data[T]]): Unit = {
    require(ps.length > 0)
    require(isCompatibleData(p, ps))

    ps match {
      case Cons(q, Nil()) => ()
      case Cons(q, qs) =>
        val dq = l1Dist(p, q.key)
        val (dq1, q1, qs1) = findMaxElem(p, qs)
        foundMaxElem(p, qs)
        assert(isUpperBoundDist(dq1, p, qs))
        if dq > dq1 then
          relaxUpperBound(dq1, dq, p, qs)
          ()
        else
          ()
    }

  } ensuring {
    isUpperBoundDist(findMaxElem(p, ps)._1, p, ps)
  }

  def findMaxElemMembership[T](p: Key, ps: List[Data[T]], tree: Tree[T], acc: List[Data[T]]): Unit = {
    require(ps.length > 0)
    require(isCompatibleData(p, ps))
    require(membership(ps, tree, acc))

    ps match {
      case Cons(q, Nil()) => ()
      case Cons(q, qs) =>
        findMaxElemMembership(p, qs, tree, acc)
        ()
    }

  } ensuring {
    membership(findMaxElem(p, ps)._3, tree, acc)
  }

  def addElem[T](k: BigInt, query: Key, p: Data[T], ps: List[Data[T]]): List[Data[T]] = {
    require(k > 0)
    require(ps.length <= k)
    require(isCompatibleData(query, ps))
    require(query.length == p.key.length)

    if ps.length < k then p :: ps
    else {
      val (d, m, ps1) = findMaxElem(query, ps)
      if l1Dist(query, p.key) > d then ps
      else p :: ps1
    }
  } ensuring { res =>
    res.length <= k &&
      res.length >= ps.length &&
      isCompatibleData(query, res)
  }

  def isCompatibleTree[T](key: Key, tree: Tree[T]): Boolean = tree match
    case Empty() => true
    case Node(data, index, left, right) =>
      key.length == data.key.length && isCompatibleTree(key, left) && isCompatibleTree(key, right)

  def membership1[T](xs: List[Data[T]], node: Node[T], acc: List[Data[T]]): Unit = {
    require(xs.forall { data => node.left.contains(data.key) || acc.contains(data) })

    xs match
      case Cons(x, xs) =>
        membership1(xs, node, acc)
      case Nil() => ()

  } ensuring {
    xs.forall { data => node.contains(data.key) || acc.contains(data) }
  }

  def membership2[T](xs: List[Data[T]], node: Node[T], acc1: List[Data[T]], acc: List[Data[T]]): Unit = {
    require(xs.forall { data => node.right.contains(data.key) || acc1.contains(data) })
    require(acc1.forall { data => node.contains(data.key) || acc.contains(data) })

    xs match
      case Cons(x, xs) =>
        membership2(xs, node, acc1, acc)
        if node.right.contains(x.key) then
          ()
        else
          assert(acc1.contains(x))
          ListSpecs.forallContained(acc1, data => node.contains(data.key) || acc.contains(data), x)
          ()
      case Nil() => ()

  } ensuring {
    xs.forall { data => node.contains(data.key) || acc.contains(data) }
  }

  def membership3[T](xs: List[Data[T]], node: Node[T], acc: List[Data[T]]): Unit = {
    require(xs.forall { data => node.right.contains(data.key) || acc.contains(data) })

    xs match
      case Cons(x, xs) =>
        membership3(xs, node, acc)
      case Nil() => ()

  } ensuring {
    xs.forall { data => node.contains(data.key) || acc.contains(data) }
  }

  def membership4[T](xs: List[Data[T]], node: Node[T], acc1: List[Data[T]], acc: List[Data[T]]): Unit = {
    require(xs.forall { data => node.left.contains(data.key) || acc1.contains(data) })
    require(acc1.forall { data => node.contains(data.key) || acc.contains(data) })

    xs match
      case Cons(x, xs) =>
        membership4(xs, node, acc1, acc)
        if node.left.contains(x.key) then
          ()
        else
          assert(acc1.contains(x))
          ListSpecs.forallContained(acc1, data => node.contains(data.key) || acc.contains(data), x)
          ()
      case Nil() => ()

  } ensuring {
    xs.forall { data => node.contains(data.key) || acc.contains(data) }
  }

  def addNewElemMembership[T](k: BigInt, query: Key,
                              data: Data[T], res: List[Data[T]],
                              tree: Node[T], acc: List[Data[T]]): Unit = {
    require(res.forall { data => tree.contains(data.key) || acc.contains(data) })
    require(tree.contains(data.key))
    require(k > 0)
    require(res.length <= k)
    require(isCompatibleData(query, res))
    require(query.length == data.key.length)

    if res.length < k then
      ()
    else
      findMaxElemMembership(query, res, tree, acc)
      ()

  } ensuring { _ =>
    addElem(k, query, data, res).forall { data => tree.contains(data.key) || acc.contains(data) }
  }

  def consContains[T](res: List[Data[T]], tree: Tree[T], x: Data[T], acc: List[Data[T]]): Unit = {
    require(res.forall { data => tree.contains(data.key) || acc.contains(data) })

    res match {
      case Nil() => ()
      case Cons(y, ys) => consContains(ys, tree, x, acc)
    }

  } ensuring { _ => res.forall { data => tree.contains(data.key) || Cons(x, acc).contains(data) } }

  def accMembership[T](tree: Tree[T], acc: List[Data[T]]): Unit = {

    acc match {
      case Nil() => ()
      case Cons(x, xs) =>
        accMembership(tree, xs)
        assert(xs.forall { data => tree.contains(data.key) || xs.contains(data) })
        consContains(xs, tree, x, xs)
    }

  } ensuring { _ =>
    acc.forall { data => tree.contains(data.key) || acc.contains(data) }
  }

  def dropEq(index: BigInt, xs: Key): Unit = {
    require(0 <= index && index < xs.length)

    if index == 0 then
      ()
    else
      dropEq(index - 1, xs.tail)

  } ensuring { _ => xs.drop(index).head == xs(index) }

  def keyOrderToHeadLt(a: Key, b: Key): Unit = {
    require(a.length == b.length)
    require(a.length > 0)
    require(keyOrder(a, b) < 0)
  } ensuring { _ => a.head <= b.head }

  def keyOrderToHeadGt(a: Key, b: Key): Unit = {
    require(a.length == b.length)
    require(a.length > 0)
    require(keyOrder(a, b) > 0)
  } ensuring { _ => a.head >= b.head }

  def keyOrderToHeadEq(a: Key, b: Key): Unit = {
    require(a.length == b.length)
    require(a.length > 0)
    require(keyOrder(a, b) == 0)
  } ensuring { _ => a.head == b.head }

  def keyOrderByToElemLt(index: BigInt, a: Key, b: Key): Unit = {
    require(a.length == b.length)
    require(0 <= index && index < a.length)
    require(keyOrderBy(index, a, b) < 0)

    dropEq(index, a)
    dropEq(index, b)
  } ensuring { _ => a(index) <= b(index) }

  def keyOrderByToElemGt(index: BigInt, a: Key, b: Key): Unit = {
    require(a.length == b.length)
    require(0 <= index && index < a.length)
    require(keyOrderBy(index, a, b) > 0)

    dropEq(index, a)
    dropEq(index, b)
  } ensuring { _ => a(index) >= b(index) }

  def crossBoundary(q: BigInt, b: BigInt, x: BigInt): Unit = {
    require(q <= b)
    require(x >= b)
  } ensuring { _ => abs(q, b) <= abs(q, x) }

  def crossBoundaryAlt(q: BigInt, b: BigInt, x: BigInt): Unit = {
    require(q >= b)
    require(x <= b)
  } ensuring { _ => abs(q, b) <= abs(q, x) }

  def isOptimal[T](res: List[Data[T]], query: Key, tree: Tree[T]): Boolean =
    require(isCompatibleData(query, res))
    tree.forall { data =>
      res.contains(data) || (query.length == data.key.length && isUpperBoundDist(l1Dist(query, data.key), query, res))
    }

  def isOptimalAmong[T](res: List[Data[T]], query: Key, trees: List[Tree[T]]): Boolean =
    require(isCompatibleData(query, res))
    trees.forall { tree => isCompatibleTree(query, tree) && isOptimal(res, query, tree) }

  def withDistLowerBound[T](query: Key, tree: Tree[T], bound: BigInt): Boolean = {
    require(isCompatibleTree(query, tree))
    tree match {
      case Empty() => true
      case Node(data, index, left, right) =>
        l1Dist(query, data.key) >= bound && withDistLowerBound(query, left, bound) && withDistLowerBound(query, right, bound)
    }
  }

  def rightTreeLowerBoundHelper[T](query: Key, index: BigInt, key: Key, t: Tree[T]): Unit = {
    require(isCompatibleTree(query, t))
    require(0 <= index && index < query.length)
    require(query.length == key.length)
    require(query(index) <= key(index))
    require(t.forallKeys(greaterThan(_, IndexedKey(index, key))))

    t match {
      case Empty() => ()
      case Node(data, _, left, right) =>
        // assert(left.forallKeys(k => greaterThan(k, IndexedKey(index, key))))
        // assert(right.forallKeys(k => greaterThan(k, IndexedKey(index, key))))
        assert(keyOrderBy(index, key, data.key) < 0)
        keyOrderByToElemLt(index, key, data.key)
        assert(key(index) <= data.key(index))
        crossBoundary(query(index), key(index), data.key(index))
        assert(abs(query(index), key(index)) <= abs(query(index), data.key(index)))
        l1DistLowerBound(query, data.key, index, abs(query(index), key(index)))
        rightTreeLowerBoundHelper(query, index, key, left)
        rightTreeLowerBoundHelper(query, index, key, right)
        ()
    }
  } ensuring { _ => withDistLowerBound(query, t, abs(query(index), key(index))) }

  def leftTreeLowerBoundHelper[T](query: Key, index: BigInt, key: Key, t: Tree[T]): Unit = {
    require(isCompatibleTree(query, t))
    require(0 <= index && index < query.length)
    require(query.length == key.length)
    require(query(index) >= key(index))
    require(t.forallKeys(lessThan(_, IndexedKey(index, key))))

    t match {
      case Empty() => ()
      case Node(data, _, left, right) =>
        // assert(left.forallKeys(k => greaterThan(k, IndexedKey(index, key))))
        // assert(right.forallKeys(k => greaterThan(k, IndexedKey(index, key))))
        assert(keyOrderBy(index, data.key, key) < 0)
        keyOrderByToElemLt(index, data.key, key)
        assert(key(index) >= data.key(index))
        crossBoundaryAlt(query(index), key(index), data.key(index))
        assert(abs(query(index), key(index)) <= abs(query(index), data.key(index)))
        l1DistLowerBound(query, data.key, index, abs(query(index), key(index)))
        leftTreeLowerBoundHelper(query, index, key, left)
        leftTreeLowerBoundHelper(query, index, key, right)
        ()
    }
  } ensuring { _ => withDistLowerBound(query, t, abs(query(index), key(index))) }

  def rightTreeLowerBound[T](query: Key, tree: Node[T]): Unit = {
    require(isCompatibleTree(query, tree))
    require(query(tree.index) <= tree.data.key(tree.index))

    rightTreeLowerBoundHelper(query, tree.index, tree.data.key, tree.right)

  } ensuring { _ => withDistLowerBound(query, tree.right, abs(query(tree.index), tree.data.key(tree.index))) }

  def leftTreeLowerBound[T](query: Key, tree: Node[T]): Unit = {
    require(isCompatibleTree(query, tree))
    require(query(tree.index) >= tree.data.key(tree.index))

    leftTreeLowerBoundHelper(query, tree.index, tree.data.key, tree.left)

  } ensuring { _ => withDistLowerBound(query, tree.left, abs(query(tree.index), tree.data.key(tree.index))) }

  def optimalInTree[T](acc: List[Data[T]], query: Key, t: Tree[T], d: BigInt): Unit = {
    require(isCompatibleTree(query, t))
    require(isCompatibleData(query, acc))
    require(isUpperBoundDist(d, query, acc))
    require(withDistLowerBound(query, t, d))

    t match
      case Empty() => ()
      case Node(data, index, left, right) =>
        assert(l1Dist(query, data.key) >= d)
        optimalInTree(acc, query, left, d)
        optimalInTree(acc, query, right, d)
        relaxUpperBound(d, l1Dist(query, data.key), query, acc)
        assert(isUpperBoundDist(l1Dist(query, data.key), query, acc))
        ()

  } ensuring { _ =>
    isOptimal(acc, query, t)
  }

  def addElemOptimalHelper[T](k: BigInt, query: Key, data: Data[T], res: List[Data[T]]): Unit = {
    require(k > 0)
    require(res.length <= k)
    require(isCompatibleData(query, res))
    require(query.length == data.key.length)

    val res1 = addElem(k, query, data, res)
    if res.length < k then
      assert(res1.contains(data))
      assert(res1.contains(data) || (query.length == data.key.length && isUpperBoundDist(l1Dist(query, data.key), query, res1)))
      ()
    else
      val (d, m, ps1) = findMaxElem(query, res)
      foundMaxElem(query, res)
      isUpperBoundDist(d, query, res)
      if l1Dist(query, data.key) > d then
        assert(res1 == res)
        relaxUpperBound(d, l1Dist(query, data.key), query, res)
        ()
      else
        ()

  } ensuring { _ =>
    val res1 = addElem(k, query, data, res)
    res1.contains(data) || (query.length == data.key.length && isUpperBoundDist(l1Dist(query, data.key), query, res1))
  }

  def findMaxContained[T](query: Key, res: List[Data[T]], elem: Data[T]): Unit = {
    require(res.length > 0)
    require(isCompatibleData(query, res))

    res match {
      case Cons(q, Nil()) => ()
      case Cons(q, qs) =>
        val dq = l1Dist(query, q.key)
        val (dq1, q1, qs1) = findMaxElem(query, qs)
        if res.contains(elem) then
          if dq > dq1 then
            ()
          else
            findMaxContained(query, qs, elem)
            ()
        else
          ()
    }

  } ensuring { _ =>
    val (d, dq, res1) = findMaxElem(query, res)
    if res contains elem then elem == dq || res1.contains(elem) else true
  }

  def findMaxContained2[T](query: Key, res: List[Data[T]], elem: Data[T]): Unit = {
    require(res.length > 0)
    require(isCompatibleData(query, res))

    res match {
      case Cons(q, Nil()) => ()
      case Cons(q, qs) =>
        val dq = l1Dist(query, q.key)
        val (dq1, q1, res1) = findMaxElem(query, qs)
        if res1.contains(elem) then
          if dq > dq1 then
            ()
          else
            findMaxContained2(query, qs, elem)
            ()
        else
          ()
    }

  } ensuring { _ =>
    val (d, dq, res1) = findMaxElem(query, res)
    if res1.contains(elem) then res.contains(elem) else true
  }

  def findMaxElemBounded[T](query: Key, res: List[Data[T]], bound: BigInt): Unit = {
    require(res.length > 0)
    require(isCompatibleData(query, res))
    require(isUpperBoundDist(bound, query, res))

    res match {
      case Cons(q, Nil()) => ()
      case Cons(q, qs) =>
        findMaxElemBounded(query, qs, bound)
        ()
    }

  } ensuring { _ =>
    val (dm, dq, res1) = findMaxElem(query, res)
    dm <= bound && isUpperBoundDist(bound, query, res1)
  }

  def findMaxElemOptimal[T](query: Key, res: List[Data[T]], t: Tree[T], p: Data[T]): Unit = {
    require(res.length > 0)
    require(query.length == p.key.length)
    require(isCompatibleData(query, res))
    require(isOptimal(res, query, t))

    val (m, dm, res1) = findMaxElem(query, res)
    require(m >= l1Dist(query, p.key))

    t match {
      case Empty() => ()
      case Node(data, index, left, right) =>
        findMaxElemOptimal(query, res, left, p)
        findMaxElemOptimal(query, res, right, p)
        findMaxContained(query, res, data)
        assert(res.contains(data) || (query.length == data.key.length && isUpperBoundDist(l1Dist(query, data.key), query, res)))

        if res contains data then
          if data == dm then
            // mq > max(res1)
            foundMaxElem(query, res)
            assert(l1Dist(query, data.key) == m)
            assert(isUpperBoundDist(m, query, res))
            findMaxElemBounded(query, res, m)
            assert(isUpperBoundDist(m, query, res1))
            ()
          else
            // res1 contains data
            ()
        else
          assert(query.length == data.key.length && isUpperBoundDist(l1Dist(query, data.key), query, res))
          findMaxElemBounded(query, res, l1Dist(query, data.key))
          ()
    }

  } ensuring { _ =>
    val (dm, m, res1) = findMaxElem(query, res)
    isOptimal(p :: res1, query, t)
  }

  def addElemOptimalHelper2[T](k: BigInt, query: Key, data: Data[T], t: Tree[T], res: List[Data[T]]): Unit = {
    require(k > 0)
    require(res.length == k)
    require(isCompatibleData(query, res))
    require(isCompatibleTree(query, t))
    require(query.length == data.key.length)
    require(isOptimal(res, query, t))

    if res.length < k then
      ()
    else
      val (d, m, ps1) = findMaxElem(query, res)
      if l1Dist(query, data.key) > d then ()
      else
        findMaxElemOptimal(query, res, t, data)
        ()

  } ensuring { _ =>
    isOptimal(addElem(k, query, data, res), query, t)
  }

  def addElemOptimalAmong[T](k: BigInt, query: Key, data: Data[T], res: List[Data[T]], trees: List[Tree[T]]): Unit = {
    require(k > 0)
    require(res.length == k)
    require(isCompatibleData(query, res))
    require(trees.forall(isCompatibleTree(query, _)))
    require(query.length == data.key.length)
    require(isOptimalAmong(res, query, trees))

    trees match {
      case Nil() => ()
      case Cons(tree, trees) =>
        addElemOptimalHelper2(k, query, data, tree, res)
        addElemOptimalAmong(k, query, data, res, trees)
    }

  } ensuring {
    isOptimalAmong(addElem(k, query, data, res), query, trees)
  }

  def addElemOptimal[T](k: BigInt, query: Key, t: Node[T], res: List[Data[T]]): Unit = {
    require(k > 0)
    require(res.length == k)
    require(isCompatibleData(query, res))
    require(isCompatibleTree(query, t))
    require(query.length == t.data.key.length)
    require(isOptimal(res, query, t.left))
    require(isOptimal(res, query, t.right))

    addElemOptimalHelper(k, query, t.data, res)
    addElemOptimalHelper2(k, query, t.data, t.left, res)
    addElemOptimalHelper2(k, query, t.data, t.right, res)

  } ensuring { _ =>
    isOptimal(addElem(k, query, t.data, res), query, t)
  }

  def extendSolutionContained[T](tree: Tree[T], data: Data[T], res: List[Data[T]]): Unit = {
    require(tree.forall(res.contains(_)))

    tree match {
      case Empty() =>
      case Node(data1, index, left, right) =>
        extendSolutionContained(left, data, res)
        extendSolutionContained(right, data, res)
    }
  } ensuring { _ =>
    tree.forall((data :: res).contains(_))
  }

  def extendSolutionContainedMany[T](trees: List[Tree[T]], data: Data[T], res: List[Data[T]]): Unit = {
    require(trees.forall(tree => tree.forall(res.contains(_))))

    trees match {
      case Nil() =>
      case Cons(tree, trees) =>
        extendSolutionContained(tree, data, res)
        extendSolutionContainedMany(trees, data, res)
    }

  } ensuring { _ =>
    trees.forall(tree => tree.forall((data :: res).contains(_)))
  }

  def nearestNeighborsSmallTree[T](k: BigInt, acc: List[Data[T]], query: Key, tree: Tree[T], accTrees: List[Tree[T]]): Unit = {
    require(isCompatibleTree(query, tree))
    require(k > 0)
    require(acc.length <= k)
    require(isCompatibleData(query, acc))
    val res = nearestNeighbors(k, acc, query, tree)
    require(res.length < k)
    require(accTrees.forall(tree => tree.forall(acc.contains(_))))

    tree match {
      case Empty() =>
        assert(tree.forall(res.contains(_)))
        assert((tree :: accTrees).forall(tree => tree.forall(res.contains(_))))
        ()
      case Node(data, index, left, right) =>
        if query(index) <= data.key(index) then
          val acc1 = nearestNeighbors(k, acc, query, left)
          if acc1.length >= k then
            assert(res.length >= k)
          else
            nearestNeighborsSmallTree(k, acc, query, left, accTrees)
            assert((left :: accTrees).forall { tree => tree.forall(acc1.contains(_)) })
            val res0 = nearestNeighbors(k, acc1, query, right)
            nearestNeighborsSmallTree(k, acc1, query, right, left :: accTrees)
            assert((right :: left :: accTrees).forall { tree => tree.forall(res0.contains(_)) })
            if res0.length >= k then
              assert(res.length >= k)
            else
              assert(res == data :: res0)
              assert(left.forall(res0.contains(_)))
              assert(right.forall(res0.contains(_)))
              extendSolutionContained(left, data, res0)
              extendSolutionContained(right, data, res0)
              assert(left.forall(res.contains(_)))
              assert(right.forall(res.contains(_)))
              assert(tree.forall(res.contains(_)))
              extendSolutionContainedMany(accTrees, data, res0)
              assert((tree :: accTrees).forall(tree => tree.forall(res.contains(_))))
              ()
        else
          val acc1 = nearestNeighbors(k, acc, query, right)
          if acc1.length >= k then
            assert(res.length >= k)
            assert((tree :: accTrees).forall(tree => tree.forall(res.contains(_))))
          else
            nearestNeighborsSmallTree(k, acc, query, right, accTrees)
            assert((right :: accTrees).forall { tree => tree.forall(acc1.contains(_)) })
            val res0 = nearestNeighbors(k, acc1, query, left)
            nearestNeighborsSmallTree(k, acc1, query, left, right :: accTrees)
            assert((left :: right :: accTrees).forall { tree => tree.forall(res0.contains(_)) })
            if res0.length >= k then
              assert(res.length >= k)
            else
              assert(res == data :: res0)
              assert(left.forall(res0.contains(_)))
              assert(right.forall(res0.contains(_)))
              extendSolutionContained(left, data, res0)
              extendSolutionContained(right, data, res0)
              assert(left.forall(res.contains(_)))
              assert(right.forall(res.contains(_)))
              assert(tree.forall(res.contains(_)))
              extendSolutionContainedMany(accTrees, data, res0)
              assert((tree :: accTrees).forall(tree => tree.forall(res.contains(_))))
            // assert((tree :: accTrees).forall(tree => tree.forall(res.contains(_))))
    }

  } ensuring { _ =>
    val res = nearestNeighbors(k, acc, query, tree)
    (tree :: accTrees).forall(tree => tree.forall(res.contains(_)))
  }

  def containedToOptimal[T](query: Key, tree: Tree[T], res: List[Data[T]]): Unit = {
    require(tree.forall(res.contains(_)))
    require(isCompatibleData(query, res))
    require(isCompatibleTree(query, tree))

    tree match {
      case Empty() =>
        ()
      case Node(data, index, left, right) =>
        containedToOptimal(query, left, res)
        containedToOptimal(query, right, res)
    }

  } ensuring { _ =>
    isOptimal(res, query, tree)
  }

  def containedToOptimalAmong[T](query: Key, trees: List[Tree[T]], res: List[Data[T]]): Unit = {
    require(trees.forall(tree => tree.forall(res.contains(_))))
    require(isCompatibleData(query, res))
    require(trees.forall(tree => isCompatibleTree(query, tree)))

    trees match {
      case Nil() =>
        ()
      case Cons(t, trees) =>
        containedToOptimalAmong(query, trees, res)
        containedToOptimal(query, t, res)
    }

  } ensuring { _ =>
    isOptimalAmong(res, query, trees)
  }

  def nearestNeighborsOptimal[T](k: BigInt, acc: List[Data[T]], query: Key, tree: Tree[T], accTrees: List[Tree[T]]): Unit = {
    require(isCompatibleTree(query, tree))
    require(k > 0)
    require(acc.length <= k)
    require(isCompatibleData(query, acc))

    require(isOptimalAmong(acc, query, accTrees))
    require(accTrees.forall(isCompatibleTree(query, _)))

    require(if acc.length < k then accTrees.forall(tree => tree.forall(acc.contains(_))) else true)

    tree match {
      case Empty() =>
        assert(nearestNeighbors(k, acc, query, tree) == acc)
        assert(isOptimal(acc, query, tree))
        ()
      case tree @ Node(data, index, left, right) =>
        if query(index) <= data.key(index) then
          val acc1 = nearestNeighbors(k, acc, query, left)
          nearestNeighborsOptimal(k, acc, query, left, accTrees)
          assert(isOptimalAmong(acc1, query, left :: accTrees))
          if acc1.length >= k then
            val (dl, l, _) = findMaxElem(query, acc1)
            foundMaxElem(query, acc1)
            assert(isUpperBoundDist(dl, query, acc1))
            if dl <= abs(query(index), data.key(index)) then
              assert(nearestNeighbors(k, acc, query, tree) == addElem(k, query, data, acc1))
              relaxUpperBound(dl, abs(query(index), data.key(index)), query, acc1)
              assert(isUpperBoundDist(abs(query(index), data.key(index)), query, acc1))
              rightTreeLowerBound(query, tree)
              assert(withDistLowerBound(query, tree.right, abs(query(index), data.key(index))))
              optimalInTree(acc1, query, tree.right, abs(query(index), data.key(index)))
              assert(isOptimalAmong(acc1, query, right :: left :: accTrees))
              addElemOptimal(k, query, tree, acc1)
              assert(isOptimal(addElem(k, query, data, acc1), query, tree))
              addElemOptimalAmong(k, query, data, acc1, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
            else
              val res0 = nearestNeighbors(k, acc1, query, right)
              nearestNeighborsOptimal(k, acc1, query, right, left :: accTrees)
              assert(isOptimalAmong(res0, query, right :: left :: accTrees))
              assert(isOptimalAmong(res0, query, left :: accTrees))
              assert(isOptimal(res0, query, right))
              assert(isOptimal(res0, query, left))
              addElemOptimal(k, query, tree, res0)
              assert(isOptimal(addElem(k, query, data, res0), query, tree))
              addElemOptimalAmong(k, query, data, res0, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
              ()
          else
            val res0 = nearestNeighbors(k, acc1, query, right)
            if acc1.length < k then
              nearestNeighborsSmallTree(k, acc, query, left, accTrees)
              nearestNeighborsOptimal(k, acc1, query, right, left :: accTrees)
            else
              nearestNeighborsOptimal(k, acc1, query, right, left :: accTrees)
            assert(isOptimalAmong(res0, query, right :: left :: accTrees))
            assert(isOptimalAmong(res0, query, left :: accTrees))
            assert(isOptimal(res0, query, right))
            assert(isOptimal(res0, query, left))
            if res0.length >= k then
              addElemOptimal(k, query, tree, res0)
              assert(isOptimal(addElem(k, query, data, res0), query, tree))
              addElemOptimalAmong(k, query, data, res0, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
              ()
            else
              // len(res0) < k
              assert(acc1.length < k)
              nearestNeighborsSmallTree(k, acc, query, left, accTrees)
              nearestNeighborsSmallTree(k, acc1, query, right, left :: accTrees)
              assert((right :: left :: accTrees).forall(tree => tree.forall(res0.contains(_))))
              extendSolutionContainedMany(right :: left :: accTrees, data, res0)
              assert((right :: left :: accTrees).forall(tree => tree.forall((data :: res0).contains(_))))
              containedToOptimalAmong(query, right :: left :: accTrees, data :: res0)
              assert(isOptimalAmong(data :: res0, query, right :: left :: accTrees))
              assert(isOptimalAmong(data :: res0, query, left :: accTrees))
              assert(isOptimalAmong(data :: res0, query, accTrees))
              assert(isOptimal(data :: res0, query, left))
              assert(isOptimal(data :: res0, query, right))
              assert((data :: res0).contains(data))
              assert(isOptimal(data :: res0, query, tree))
              ()
        else
          val acc1 = nearestNeighbors(k, acc, query, right)
          nearestNeighborsOptimal(k, acc, query, right, accTrees)
          assert(isOptimalAmong(acc1, query, right :: accTrees))
          if acc1.length >= k then
            val (dl, l, _) = findMaxElem(query, acc1)
            foundMaxElem(query, acc1)
            assert(isUpperBoundDist(dl, query, acc1))
            if dl <= abs(query(index), data.key(index)) then
              assert(nearestNeighbors(k, acc, query, tree) == addElem(k, query, data, acc1))
              relaxUpperBound(dl, abs(query(index), data.key(index)), query, acc1)
              assert(isUpperBoundDist(abs(query(index), data.key(index)), query, acc1))
              leftTreeLowerBound(query, tree)
              assert(withDistLowerBound(query, tree.left, abs(query(index), data.key(index))))
              optimalInTree(acc1, query, tree.left, abs(query(index), data.key(index)))
              assert(isOptimalAmong(acc1, query, left :: right :: accTrees))
              addElemOptimal(k, query, tree, acc1)
              assert(isOptimal(addElem(k, query, data, acc1), query, tree))
              addElemOptimalAmong(k, query, data, acc1, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
            else
              val res0 = nearestNeighbors(k, acc1, query, left)
              nearestNeighborsOptimal(k, acc1, query, left, right :: accTrees)
              assert(isOptimalAmong(res0, query, left :: right :: accTrees))
              assert(isOptimalAmong(res0, query, right :: accTrees))
              assert(isOptimal(res0, query, right))
              assert(isOptimal(res0, query, left))
              addElemOptimal(k, query, tree, res0)
              assert(isOptimal(addElem(k, query, data, res0), query, tree))
              addElemOptimalAmong(k, query, data, res0, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
          else
            val res0 = nearestNeighbors(k, acc1, query, left)
            if acc1.length < k then
              nearestNeighborsSmallTree(k, acc, query, right, accTrees)
              nearestNeighborsOptimal(k, acc1, query, left, right :: accTrees)
            else
              nearestNeighborsOptimal(k, acc1, query, left, right :: accTrees)
            assert(isOptimalAmong(res0, query, left :: right :: accTrees))
            assert(isOptimalAmong(res0, query, right :: accTrees))
            assert(isOptimal(res0, query, right))
            assert(isOptimal(res0, query, left))
            if res0.length >= k then
              addElemOptimal(k, query, tree, res0)
              assert(isOptimal(addElem(k, query, data, res0), query, tree))
              addElemOptimalAmong(k, query, data, res0, accTrees)
              // assert(isOptimal(nearestNeighbors(k, acc, query, tree), query, tree))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
            else
              // len(res0) < k
              assert(acc1.length < k)
              nearestNeighborsSmallTree(k, acc, query, right, accTrees)
              nearestNeighborsSmallTree(k, acc1, query, left, right :: accTrees)
              assert((left :: right :: accTrees).forall(tree => tree.forall(res0.contains(_))))
              extendSolutionContainedMany(left :: right :: accTrees, data, res0)
              assert((left :: right :: accTrees).forall(tree => tree.forall((data :: res0).contains(_))))
              containedToOptimalAmong(query, left :: right :: accTrees, data :: res0)
              assert(isOptimalAmong(data :: res0, query, left :: right :: accTrees))
              assert(isOptimalAmong(data :: res0, query, right :: accTrees))
              assert(isOptimal(data :: res0, query, left))
              assert(isOptimal(data :: res0, query, right))
              assert((data :: res0).contains(data))
              assert(isOptimal(data :: res0, query, tree))
              assert(nearestNeighbors(k, acc, query, tree) == data :: res0)
              assert(isOptimalAmong(data :: res0, query, accTrees))
              assert(isOptimalAmong(data :: res0, query, tree :: accTrees))
              assert(isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees))
    }

  } ensuring { _ =>
    isOptimalAmong(nearestNeighbors(k, acc, query, tree), query, tree :: accTrees)
  }

  def nearestNeighbors[T](k: BigInt, acc: List[Data[T]], query: Key, tree: Tree[T]): List[Data[T]] = {
    require(isCompatibleTree(query, tree))
    require(k > 0)
    require(acc.length <= k)
    require(isCompatibleData(query, acc))

    tree match {
      case Empty() =>
        accMembership(tree, acc)
        assert(acc.forall { data => tree.contains(data.key) || acc.contains(data) })
        // assert(isOptimal(acc, query, tree))
        acc
      case node @ Node(data, index, left, right) =>
        val res =
          if query(index) <= data.key(index) then {
            val acc1 = nearestNeighbors(k, acc, query, left)
            assert(acc1.forall { data => left.contains(data.key) || acc.contains(data) })
            membership1(acc1, node, acc)
            assert(acc1.forall { data => node.contains(data.key) || acc.contains(data) })

            assert(acc1.length >= acc.length)

            // assert(isOptimal(acc1, query, left))
            if acc1.length >= k then
              val (dl, l, _) = findMaxElem(query, acc1)
              if dl <= abs(query(index), data.key(index)) then
                acc1
              else
                val res0 = nearestNeighbors(k, acc1, query, right)
                assert(res0.forall { data => right.contains(data.key) || acc1.contains(data) })
                membership2(res0, node, acc1, acc)
                assert(res0.forall { data => node.contains(data.key) || acc.contains(data) })
                res0
            else
              val res0 = nearestNeighbors(k, acc1, query, right)
              assert(res0.forall { data => right.contains(data.key) || acc1.contains(data) })
              membership2(res0, node, acc1, acc)
              assert(res0.forall { data => node.contains(data.key) || acc.contains(data) })
              res0
          } else {
            val acc1 = nearestNeighbors(k, acc, query, right)
            assert(acc1.forall { data => right.contains(data.key) || acc.contains(data) })
            membership3(acc1, node, acc)
            assert(acc1.forall { data => node.contains(data.key) || acc.contains(data) })
            if acc1.length >= k then
              val (dl, l, _) = findMaxElem(query, acc1)
              if dl <= abs(query(index), data.key(index)) then
                acc1
              else
                val res0 = nearestNeighbors(k, acc1, query, left)
                assert(res0.forall { data => left.contains(data.key) || acc1.contains(data) })
                membership4(res0, node, acc1, acc)
                assert(res0.forall { data => node.contains(data.key) || acc.contains(data) })
                res0
            else
              val res0 = nearestNeighbors(k, acc1, query, left)
              assert(res0.forall { data => left.contains(data.key) || acc1.contains(data) })
              membership4(res0, node, acc1, acc)
              assert(res0.forall { data => node.contains(data.key) || acc.contains(data) })
              res0
          }
        assert(res.length >= acc.length)
        assert(res.forall { data => node.contains(data.key) || acc.contains(data) })
        val res0 = addElem(k, query, data, res)
        assert(res0.length >= acc.length)
        addNewElemMembership(k, query, data, res, node, acc)
        assert(res0.forall { data => node.contains(data.key) || acc.contains(data) })
        res0
    }
  } ensuring { res =>
    res.length <= k &&
      res.length >= acc.length &&
      isCompatibleData(query, res) &&
      res.forall { data => tree.contains(data.key) || acc.contains(data) }
  }

  def nearestNeighborsIsOptimal[T](k: BigInt, query: Key, tree: Tree[T]): Unit = {
      require(isCompatibleTree(query, tree))
      require(k > 0)

      nearestNeighborsOptimal(k, Nil(), query, tree, Nil())
  } ensuring { _ =>
    isOptimalAmong(nearestNeighbors(k, Nil(), query, tree), query, tree :: Nil())
  }

  def nearestNeighborsMembership[T](k: BigInt, query: Key, tree: Tree[T]): Unit = {
      require(isCompatibleTree(query, tree))
      require(k > 0)
  } ensuring { _ =>
    val res = nearestNeighbors(k, Nil(), query, tree)
    res.length <= k &&
      res.forall { data => tree.contains(data.key) || Nil().contains(data) }
  }

  def totalSizeOf[T](trees: List[Tree[T]]): BigInt =
    trees match
      case Nil() => BigInt(0)
      case Cons(tree, trees) => tree.size + totalSizeOf(trees)

  def relaxTotalSizeOf[T](tree0: Tree[T], tree1: Tree[T], trees: List[Tree[T]]): Unit = {
    require(tree0.size <= tree1.size)
  } ensuring { _ =>
    totalSizeOf(tree0 :: trees) <= totalSizeOf(tree1 :: trees)
  }

  def min(a: BigInt, b: BigInt): BigInt =
    if a >= b then b else a

  def elimMin(a: BigInt, b: BigInt): Unit = {
    if a >= b then ()
    else ()
  } ensuring { _ =>
    min(a, b) <= a && min(a, b) <= b
  }

  def addElemSize[T](k: BigInt, query: Key, p: Data[T], ps: List[Data[T]]): Unit = {
    require(k > 0)
    require(ps.length <= k)
    require(isCompatibleData(query, ps))
    require(query.length == p.key.length)

    if ps.length < k then ()
    else ()

  } ensuring { _ =>
    val res = addElem(k, query, p, ps)
    if ps.length < k then res.length == ps.length + 1 && res.length <= k
    else res.length == k
  }

  def minRelaxRight(a: BigInt, b: BigInt, b1: BigInt): Unit = {
    require(a == min(a, b))
    require(b <= b1)
    if a >= b then () else ()
  } ensuring { _ =>
    a == min(a, b1)
  }

  def treeSizeLeft[T](tree: Node[T]): Unit = {
  } ensuring { _ =>
    tree.left.size < tree.size
  }

  def treeSizeRight[T](tree: Node[T]): Unit = {
  } ensuring { _ =>
    tree.right.size < tree.size
  }

  def nearestNeighborsSizeHelper[T](k: BigInt,
                                    acc: List[Data[T]],
                                    query: Key, tree: Tree[T],
                                    accTrees: List[Tree[T]]): Unit = {
    require(isCompatibleTree(query, tree))
    require(k > 0)
    require(acc.length <= k)
    require(isCompatibleData(query, acc))

    require(acc.length == min(k, totalSizeOf(accTrees)))

    tree match
      case Empty() =>
        ()
      case tree @ Node(data, index, left, right) =>
        if query(index) <= data.key(index) then
          val acc1 = nearestNeighbors(k, acc, query, left)
          nearestNeighborsSizeHelper(k, acc, query, left, accTrees)
          // assert(acc1.length == min(k, totalSizeOf(left :: accTrees)))
          if acc1.length >= k then
            val (dl, l, _) = findMaxElem(query, acc1)
            if dl <= abs(query(index), data.key(index)) then
              // addElem(k, query, data, acc1)
              addElemSize(k, query, data, acc1)
              // res.length == k
              // min(k, totalSizeOf(left :: accTrees)) == k
              // ==> min(k, totalSizeOf(tree :: accTrees)) == k
              assert(min(k, totalSizeOf(left :: accTrees)) == k)
              treeSizeLeft(tree)
              minRelaxRight(k, totalSizeOf(left :: accTrees), totalSizeOf(tree :: accTrees))
            else
              val res0 = nearestNeighbors(k, acc1, query, right)
              nearestNeighborsSizeHelper(k, acc1, query, right, left :: accTrees)
              // assert(res0.length == min(k, totalSizeOf(right :: left :: accTrees)))
              addElemSize(k, query, data, res0)
              if res0.length < k then
                ()
              else
                assert(min(k, totalSizeOf(right :: left :: accTrees)) == k)
                assert(tree.size > right.size + left.size)
                minRelaxRight(k, totalSizeOf(right :: left :: accTrees), totalSizeOf(tree :: accTrees))
          else
            val res0 = nearestNeighbors(k, acc1, query, right)
            nearestNeighborsSizeHelper(k, acc1, query, right, left :: accTrees)
            // assert(res0.length == min(k, totalSizeOf(right :: left :: accTrees)))
            addElemSize(k, query, data, res0)
            if res0.length < k then
              ()
            else
              assert(min(k, totalSizeOf(right :: left :: accTrees)) == k)
              assert(tree.size > right.size + left.size)
              minRelaxRight(k, totalSizeOf(right :: left :: accTrees), totalSizeOf(tree :: accTrees))
        else
          val acc1 = nearestNeighbors(k, acc, query, right)
          nearestNeighborsSizeHelper(k, acc, query, right, accTrees)
          // assert(acc1.length == min(k, totalSizeOf(right :: accTrees)))
          if acc1.length >= k then
            val (dl, l, _) = findMaxElem(query, acc1)
            if dl <= abs(query(index), data.key(index)) then
              // addElem(k, query, data, acc1)
              addElemSize(k, query, data, acc1)
              // res.length == k
              // min(k, totalSizeOf(right :: accTrees)) == k
              // ==> min(k, totalSizeOf(tree :: accTrees)) == k
              assert(min(k, totalSizeOf(right :: accTrees)) == k)
              treeSizeLeft(tree)
              minRelaxRight(k, totalSizeOf(right :: accTrees), totalSizeOf(tree :: accTrees))
            else
              val res0 = nearestNeighbors(k, acc1, query, left)
              nearestNeighborsSizeHelper(k, acc1, query, left, right :: accTrees)
              // assert(res0.length == min(k, totalSizeOf(left :: right :: accTrees)))
              addElemSize(k, query, data, res0)
              if res0.length < k then
                ()
              else
                assert(min(k, totalSizeOf(left :: right :: accTrees)) == k)
                assert(tree.size > left.size + right.size)
                minRelaxRight(k, totalSizeOf(left :: right :: accTrees), totalSizeOf(tree :: accTrees))
          else
            val res0 = nearestNeighbors(k, acc1, query, left)
            nearestNeighborsSizeHelper(k, acc1, query, left, right :: accTrees)
            // assert(res0.length == min(k, totalSizeOf(left :: right :: accTrees)))
            addElemSize(k, query, data, res0)
            if res0.length < k then
              ()
            else
              assert(min(k, totalSizeOf(left :: right :: accTrees)) == k)
              assert(tree.size > left.size + right.size)
              minRelaxRight(k, totalSizeOf(left :: right :: accTrees), totalSizeOf(tree :: accTrees))

  } ensuring { _ =>
    val res = nearestNeighbors(k, acc, query, tree)
    res.length == min(k, totalSizeOf(tree :: accTrees))
  }

  def nearestNeighborsSize[T](k: BigInt,
                              query: Key, tree: Tree[T]): Unit = {
    require(isCompatibleTree(query, tree))
    require(k > 0)
    nearestNeighborsSizeHelper(k, Nil(), query, tree, Nil())

  } ensuring { _ =>
    val res = nearestNeighbors(k, Nil(), query, tree)
    res.length == min(k, tree.size)
  }

  def nearestNeighbors[T](k: BigInt, query: Key, tree: Tree[T]): List[Data[T]] =
    nearestNeighbors(k, Nil(), query, tree)
}

