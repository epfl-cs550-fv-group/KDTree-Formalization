import stainless.lang._
import stainless.collection._

def showTree(tree: Tree[String]): Unit = {
  val sb = StringBuilder()
  var freshCount: Int = 0
  def freshEmptyName: String =
    freshCount += 1
    s"e$freshCount"

  def keyToPos(key: Key): String = key.map(_.toString).toScala.mkString(",") ++ "!"
  def keyToPosPretty(key: Key): String = key.map(_.toString).toScala.mkString(", ")
  def recur(node: Tree[String], parent: Option[String] = None()): Unit =
    node match
      case Empty() =>
      case Node(Data(key, value), index, left, right) =>
        sb ++= s"  $value [label=\"$value\\n(${keyToPosPretty(key)})\\nindex=$index\" shape=\"circle\"]\n"
        parent.map { p =>
          sb ++= s"  $p -> $value\n"
        }
        recur(left, Some(value))
        recur(right, Some(value))
  sb ++= s"strict digraph {\n"
  recur(tree)
  sb ++= s"}\n"
  println(sb.result)
}

@main def example: Unit = {
  val xs = List(
    Data(List[BigInt](5, 5), "a"),
    Data(List[BigInt](2, 7), "b"),
    Data(List[BigInt](5, 10), "c"),
    Data(List[BigInt](0, 8), "d"),
    Data(List[BigInt](12, 0), "e"),
    Data(List[BigInt](6, 7), "f"),
  )

  /* optimal construction */
  val tree = optimalConstruct(xs)
  showTree(tree)
  for data <- xs.toScala do
    assert(tree.query(data.key) == Some(data.value))

  /* insertion */
  val tree1 = tree.insert(Data(List[BigInt](10, 10), "g"), 1)
  showTree(tree1)
  assert(tree1.query(List[BigInt](10, 10)) == Some("g"))

  /* erasure */
  val tree2 = tree1.erase(List[BigInt](10, 10))
  showTree(tree2)
  assert(tree2.query(List[BigInt](10, 10)) == None())

  /* region search */
  assert(
    tree2.regionSearch(List[BigInt](10, 10), List[BigInt](5, 5)).map(_.key) == List(
      List[BigInt](5, 5),
      List[BigInt](5, 10),
      List[BigInt](6, 7),
    )
  )

  /* nearest neighbors query */
  assert(
    NNQ.nearestNeighbors(3, List[BigInt](0, 0), tree2).map(_.key) == List(
      List[BigInt](2, 7),
      List[BigInt](0, 8),
      List[BigInt](5, 5),
    )
  )
}
