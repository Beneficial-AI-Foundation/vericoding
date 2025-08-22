//ATOM Tree
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//ATOM 
predicate BinarySearchTree(tree: Tree)
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

// ATOM 
predicate maxValue(tree: Tree, max: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

// ATOM 
predicate minValue(tree: Tree, min: int)
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

//IMPL insertRecursion
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  match tree
  case Empty => 
    res := Node(Empty, value, Empty);
  case Node(left, v, right) =>
    if value < v {
      var newLeft := insertRecursion(left, value);
      res := Node(newLeft, v, right);
    } else if value > v {
      var newRight := insertRecursion(right, value);
      res := Node(left, v, newRight);
    } else {
      res := tree;
    }
}