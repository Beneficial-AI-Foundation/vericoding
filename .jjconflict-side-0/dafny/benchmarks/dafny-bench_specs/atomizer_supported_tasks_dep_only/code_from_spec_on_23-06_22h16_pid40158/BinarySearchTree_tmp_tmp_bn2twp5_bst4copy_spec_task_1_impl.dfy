//ATOM Tree
datatype Tree = Empty | Node(left: Tree, data: int, right: Tree)

//ATOM BinarySearchTree
predicate BinarySearchTree(tree: Tree)
{
  match tree
  case Empty => true
  case Node(left, data, right) =>
    BinarySearchTree(left) && BinarySearchTree(right) &&
    (left != Empty ==> maxValue(left) < data) &&
    (right != Empty ==> minValue(right) > data)
}

//ATOM maxValue
function maxValue(tree: Tree): int
  requires tree != Empty
{
  match tree
  case Node(left, data, Empty) => data
  case Node(left, data, right) => maxValue(right)
}

//ATOM minValue
function minValue(tree: Tree): int
  requires tree != Empty
{
  match tree
  case Node(Empty, data, right) => data
  case Node(left, data, right) => minValue(left)
}

//IMPL GetMin
method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  requires BinarySearchTree(tree)
  ensures res == minValue(tree)
{
  var current := tree;
  /* code modified by LLM (iteration 1): Fixed loop condition and added proper invariants for BST traversal */
  while current.Node? && current.left != Empty
    invariant current != Empty
    invariant BinarySearchTree(current)
    invariant minValue(current) == minValue(tree)
  {
    current := current.left;
  }
  /* code modified by LLM (iteration 1): Return the data of the leftmost node */
  res := current.data;
}

//ATOM GetMax
method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  requires BinarySearchTree(tree)
  ensures res == maxValue(tree)
{
  var current := tree;
  while current.right != Empty
    invariant current != Empty
    invariant BinarySearchTree(current)
    invariant maxValue(current) == maxValue(tree)
  {
    current := current.right;
  }
  res := current.data;
}

//ATOM insert
method insert(tree: Tree, value: int) returns (result: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(result)
{
  result := insertRecursion(tree, value);
}

//ATOM insertRecursion
function insertRecursion(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(insertRecursion(tree, value))
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, data, right) =>
    if value <= data then
      Node(insertRecursion(left, value), data, right)
    else
      Node(left, data, insertRecursion(right, value))
}

//ATOM delete
method delete(tree: Tree, value: int) returns (result: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(result)
{
  result := match tree
  case Empty => Empty
  case Node(left, data, right) =>
    if value < data then
      Node(delete(left, value), data, right)
    else if value > data then
      Node(left, data, delete(right, value))
    else
      if left == Empty then right
      else if right == Empty then left
      else
        var minRight := minValue(right);
        Node(left, minRight, delete(right, minRight))
}

//ATOM Inorder
method Inorder(tree: Tree) returns (result: seq<int>)
{
  match tree
  case Empty => result := [];
  case Node(left, data, right) =>
    var leftSeq := Inorder(left);
    var rightSeq := Inorder(right);
    result := leftSeq + [data] + rightSeq;
}

//ATOM Postorder
method Postorder(tree: Tree) returns (result: seq<int>)
{
  match tree
  case Empty => result := [];
  case Node(left, data, right) =>
    var leftSeq := Postorder(left);
    var rightSeq := Postorder(right);
    result := leftSeq + rightSeq + [data];
}

//ATOM Main
method Main()
{
  var tree := Node(Node(Empty, 1, Empty), 5, Node(Empty, 7, Empty));
  var min := GetMin(tree);
  var max := GetMax(tree);
  print "Min: ", min, ", Max: ", max, "\n";
}