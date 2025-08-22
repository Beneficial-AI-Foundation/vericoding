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

//ATOM GetMin
method GetMin(tree: Tree) returns (min: int)
  requires tree != Empty
  ensures min == minValue(tree)
{
  match tree
  case Node(Empty, data, right) => min := data;
  case Node(left, data, right) => min := GetMin(left);
}

//ATOM GetMax
method GetMax(tree: Tree) returns (max: int)
  requires tree != Empty
  ensures max == maxValue(tree)
{
  match tree
  case Node(left, data, Empty) => max := data;
  case Node(left, data, right) => max := GetMax(right);
}

//ATOM insert
method insert(tree: Tree, value: int) returns (newTree: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(newTree)
{
  newTree := insertRecursion(tree, value);
}

//ATOM insertRecursion
method insertRecursion(tree: Tree, value: int) returns (newTree: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(newTree)
{
  match tree
  case Empty => newTree := Node(Empty, value, Empty);
  case Node(left, data, right) =>
    if value < data {
      var newLeft := insertRecursion(left, value);
      newTree := Node(newLeft, data, right);
    } else if value > data {
      var newRight := insertRecursion(right, value);
      newTree := Node(left, data, newRight);
    } else {
      newTree := tree;
    }
}

//ATOM delete
method delete(tree: Tree, value: int) returns (newTree: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(newTree)
{
  match tree
  case Empty => newTree := Empty;
  case Node(left, data, right) =>
    if value < data {
      var newLeft := delete(left, value);
      newTree := Node(newLeft, data, right);
    } else if value > data {
      var newRight := delete(right, value);
      newTree := Node(left, data, newRight);
    } else {
      if left == Empty {
        newTree := right;
      } else if right == Empty {
        newTree := left;
      } else {
        var successor := GetMin(right);
        var newRight := delete(right, successor);
        newTree := Node(left, successor, newRight);
      }
    }
}

//IMPL Inorder
method Inorder(tree: Tree)
  /* code modified by LLM (iteration 1): added decreases clause for termination proof */
  decreases tree
{
  match tree
  case Empty => {}
  case Node(left, data, right) =>
    Inorder(left);
    print data, " ";
    Inorder(right);
}

//ATOM Postorder
method Postorder(tree: Tree)
{
  match tree
  case Empty => {}
  case Node(left, data, right) =>
    Postorder(left);
    Postorder(right);
    print data, " ";
}

//ATOM Main
method Main()
{
  var tree := Node(Node(Empty, 2, Empty), 5, Node(Empty, 8, Empty));
  print "Inorder: ";
  Inorder(tree);
  print "\nPostorder: ";
  Postorder(tree);
  print "\n";
}