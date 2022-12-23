import stainless.lang._
import stainless.collection._
import scala.annotation.meta.companionMethod
import scala.quoted.*

extension [T](tree: Tree[T]) {

  def containsDataList(lst: List[Data[T]]): Boolean = lst match {
    case Nil() => true
    case Cons(h, t) => tree.contains(h.key) && tree.containsDataList(t)
  }

  def allData: List[Data[T]] = tree match {
    case Empty() => List()
    case Node(data, index, left, right) => 
      left.allData ++ List(data) ++ right.allData
  } ensuring (r => r.length == tree.size)

  def inAndOutRegionList(kueb: Key, kleb: Key): (List[Data[T]], List[Data[T]]) = {
    require(kueb.length == kleb.length)
    require(tree.compatible(kueb) && tree.compatible(kleb))
    require(eachGreaterThanEq(kueb, kleb))

    tree match {
      case Empty() => (List[Data[T]](), List[Data[T]]())
      case n @ Node(d, index, left, right) => {
        /** root node */
        val rRoot = {
          if inRegion(d.key, kueb, kleb) then (List(d), List[Data[T]]())
          else (List[Data[T]](), List(d))
        }
        
        assert(rRoot._1.content ++ rRoot._2.content == Set(d))
        assert(containsDataList(List(d)))
        // assert(containsDataList(List[Data[T]]()))
        assert(containsDataList(rRoot._1))
        assert(containsDataList(rRoot._2))

        if inRegion(d.key, kueb, kleb) then 
          assert(List(d).forall(d => inRegionWithPrecond(d.key, kueb, kleb)))
          assert(rRoot._2.isEmpty)
        else 
          assert(!inRegion(d.key, kueb, kleb))
          assert(rRoot._1.isEmpty)
          assert(List(d).forall(d => notInRegionWithPrecond(d.key, kueb, kleb)))

        assert(rRoot._1.isEmpty || (!rRoot._1.isEmpty && rRoot._1.forall(d => inRegionWithPrecond(d.key, kueb, kleb))))
        assert(rRoot._2.isEmpty || (!rRoot._2.isEmpty && rRoot._2.forall(d => notInRegionWithPrecond(d.key, kueb, kleb))))

        /** left and right */
        allChildrenSameLength(n)
        val rLeft = left.inAndOutRegionList(kueb, kleb)
        val rRight = right.inAndOutRegionList(kueb, kleb)

        val r = (rLeft._1 ++ rRoot._1 ++ rRight._1, rLeft._2 ++ rRoot._2 ++ rRight._2)
        assert(r._1.content ++ r._2.content == left.allData.content ++ Set(d) ++ right.allData.content)
        assert(allData.content == left.allData.content ++ Set(d) ++ right.allData.content)
        assert(r._1.content ++ r._2.content == allData.content)

        childrenContainsDataList(n, rLeft._1)
        childrenContainsDataList(n, rRight._1)
        containsDataListAppend(n, rLeft._1, rRoot._1)
        containsDataListAppend(n, rLeft._1 ++ rRoot._1, rRight._1)
        assert(n.containsDataList(r._1))
        
        childrenContainsDataList(n, rLeft._2)
        childrenContainsDataList(n, rRight._2)
        containsDataListAppend(n, rLeft._2, rRoot._2)
        containsDataListAppend(n, rLeft._2 ++ rRoot._2, rRight._2)
        assert(n.containsDataList(r._2))

        // IH: rLeft._1.isEmpty || !rLeft._1.isEmpty && rLeft._1.forall(d => inRegionWithPrecond(d.key, kueb, kleb))
        // IH: rRight._1.isEmpty || !rRight._1.isEmpty && rRight._1.forall(d => inRegionWithPrecond(d.key, kueb, kleb))
        val v0 = listConcatCond(rLeft._1, rRoot._1, d => inRegionWithPrecond(d.key, kueb, kleb))
        val v1 = listConcatCond(v0,      rRight._1, d => inRegionWithPrecond(d.key, kueb, kleb))
        assert(r._1 == v1)

        val v2 = listConcatCond(rLeft._2, rRoot._2, d => notInRegionWithPrecond(d.key, kueb, kleb))
        val v3 = listConcatCond(v2,      rRight._2, d => notInRegionWithPrecond(d.key, kueb, kleb))
        assert(r._2 == v3)

        r
      }
    }

  } ensuring (r =>
    (r._1.content ++ r._2.content == allData.content)
    && containsDataList(r._1)
    && containsDataList(r._2)
    && (r._1.isEmpty || (!r._1.isEmpty && r._1.forall(d => inRegionWithPrecond(d.key, kueb, kleb)))) 
    && (r._2.isEmpty || (!r._2.isEmpty && r._2.forall(d => notInRegionWithPrecond(d.key, kueb, kleb))))
  )

  def inRegionList(kueb: Key, kleb: Key): List[Data[T]] = {
    require(kueb.length == kleb.length)
    require(tree.compatible(kueb) && tree.compatible(kleb))
    require(eachGreaterThanEq(kueb, kleb))
    inAndOutRegionList(kueb, kleb)._1
  } 

  def regionSearch(kueb: Key, kleb: Key): List[Data[T]] = {
    require(kueb.length == kleb.length)
    require(tree.compatible(kueb) && tree.compatible(kleb))
    require(eachGreaterThanEq(kueb, kleb))

    tree match {
      case Empty() => List[Data[T]]()
      case n @ Node(d, index, left, right) => 
        val rRoot = if inRegion(d.key, kueb, kleb) then List(d) else List[Data[T]]()
        
        allChildrenSameLength(n)

        if keyOrderBy(index, d.key, kleb) < 0 then 
          n.inRegionListLeftEmpty(kueb, kleb)
          assert(left.inRegionList(kueb, kleb).isEmpty)
          rRoot ++ right.regionSearch(kueb, kleb)

        else if keyOrderBy(index, d.key, kueb) > 0 then
          n.inRegionListRightEmpty(kueb, kleb)
          assert(right.inRegionList(kueb, kleb).isEmpty)
          left.inRegionList(kueb, kleb) ++ rRoot
        
        else 
          left.regionSearch(kueb, kleb) ++ rRoot ++ right.regionSearch(kueb, kleb)
    }
    
  } ensuring (r => r == inRegionList(kueb, kleb))
}


def inRegion(k: Key, kueb: Key, kleb: Key): Boolean = {
  require(k.length == kueb.length)
  require(k.length == kleb.length)
  require(eachGreaterThanEq(kueb, kleb))
  eachLessThanEq(k, kueb) && eachGreaterThanEq(k, kleb)
}

def inRegionWithPrecond(k: Key, kueb: Key, kleb: Key): Boolean = {
  k.length == kueb.length && k.length == kleb.length && eachGreaterThanEq(kueb, kleb) 
  && inRegion(k, kueb, kleb)
}

def notInRegionWithPrecond(k: Key, kueb: Key, kleb: Key): Boolean = {
  k.length == kueb.length && k.length == kleb.length && eachGreaterThanEq(kueb, kleb) 
  && !inRegion(k, kueb, kleb)
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

extension [T](n: Node[T]) {

  def inRegionListLeftEmpty(kueb: Key, kleb: Key): Unit = {
    require(kueb.length == kleb.length)
    require(n.compatible(kueb) && n.compatible(kleb))
    require(eachGreaterThanEq(kueb, kleb))

    val (index, data, left, right) = (n.index, n.data, n.left, n.right)
    require(keyOrderBy(index, data.key, kleb) < 0)

    val cond = (k: Key) => lessThan(k, IndexedKey(index, data.key))
    assert(left.forallKeys(cond))

    val r = left.inRegionList(kueb, kleb)
    assert(left.containsDataList(r))
    assert(r.isEmpty || (!r.isEmpty && r.forall(d => inRegionWithPrecond(d.key, kueb, kleb))))

    r match {
      case Nil() => assert(r.isEmpty)
      case Cons(h, t) => 
        assert(!r.isEmpty && r.forall(d => inRegionWithPrecond(d.key, kueb, kleb)))
        // !eachGreaterThanEq(h.key, kleb)
        assert(left.contains(h.key))
        extractForAll(left, h.key, cond)
        assert(keyOrderBy(index, h.key, data.key) < 0)
        keyOrderByAssoc(index, h.key, data.key, kleb)
        assert(!eachGreaterThanEq(h.key, kleb))
        // eachGreaterThanEq(h.key, kleb))
        assert(inRegionWithPrecond(h.key, kueb, kleb))
        assert(eachGreaterThanEq(h.key, kleb))
        // conflict
        assert(eachGreaterThanEq(h.key, kleb) && !eachGreaterThanEq(h.key, kleb))
    }
    assert(r.isEmpty)
  } ensuring (_ => n.left.inRegionList(kueb, kleb).isEmpty)

  def inRegionListRightEmpty(kueb: Key, kleb: Key): Unit = {
    require(kueb.length == kleb.length)
    require(n.compatible(kueb) && n.compatible(kleb))
    require(eachGreaterThanEq(kueb, kleb))

    val (index, data, left, right) = (n.index, n.data, n.left, n.right)
    require(keyOrderBy(index, data.key, kueb) > 0)

    val cond = (k: Key) => greaterThan(k, IndexedKey(index, data.key))
    assert(right.forallKeys(cond))

    val r = right.inRegionList(kueb, kleb)
    assert(right.containsDataList(r))
    assert(r.isEmpty || (!r.isEmpty && r.forall(d => inRegionWithPrecond(d.key, kueb, kleb))))

    r match {
      case Nil() => assert(r.isEmpty)
      case Cons(h, t) => 
        assert(!r.isEmpty && r.forall(d => inRegionWithPrecond(d.key, kueb, kleb)))
        // !eachLessThanEq(h.key, kueb)
        assert(right.contains(h.key))
        extractForAll(right, h.key, cond)
        assert(cond(h.key))
        assert(keyOrderBy(index, data.key, h.key) < 0) // data.key < h.key
        keyOrderByAntisym(index, data.key, kueb) // kueb < data.key
        keyOrderByAssoc(index, kueb, data.key, h.key) // kueb < h.key
        keyOrderByAntisymNeg(index, kueb, h.key) // h.key > kueb
        assert(keyOrderBy(index, h.key, kueb) > 0)
        assert(!eachLessThanEq(h.key, kueb))
        // eachLessThanEq(h.key, kueb))
        assert(inRegionWithPrecond(h.key, kueb, kleb))
        assert(eachLessThanEq(h.key, kueb))
        // conflict
        assert(eachLessThanEq(h.key, kueb) && !eachLessThanEq(h.key, kueb))
    }
    assert(r.isEmpty)
  } ensuring (_ => n.right.inRegionList(kueb, kleb).isEmpty)
}

def childrenContainsDataList[T](t: Node[T], lst: List[Data[T]]): Unit = {
  require(t.left.containsDataList(lst) || t.right.containsDataList(lst))

  lst match {
    case Nil() => assert(t.containsDataList(lst))
    case Cons(head, tail) => {
      assert(t.left.contains(head.key) || t.right.contains(head.key))
      assert(t.contains(head.key))
      assert(t.left.containsDataList(tail) || t.right.containsDataList(tail))
      childrenContainsDataList(t, tail)
      // IH: t.containsList(tail)
      assert(t.containsDataList(lst))
    }
  }

} ensuring (t.containsDataList(lst))

def containsDataListAppend[T](t: Tree[T], l0: List[Data[T]], l1: List[Data[T]]): Unit = {
  require(t.containsDataList(l0))
  require(t.containsDataList(l1))

  l0 match {
    case Nil() => assert(l0 ++ l1 == l1)
    case Cons(h0, t0) => {
      assert(t.contains(h0.key) && t.containsDataList(t0))
      containsDataListAppend(t, t0, l1)
    }
  }

} ensuring (t.containsDataList(l0 ++ l1))
