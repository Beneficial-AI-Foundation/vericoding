//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)


//ATOM

method GetMin(tree: Tree) returns (res: int)
{
  res := 0;
  return res;
}


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


//ATOM

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}


//ATOM

predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}


//IMPL delete

method delete(tree: Tree, value: int) returns (res: Tree)
 requires BinarySearchTree(tree)
 //ensures BinarySearchTree(res)
 //ensures res != Empty ==> BinarySearchTree(res)
{
  match tree {
    case Empty => 
      res := Empty;
    case Node(left, v, right) =>
      if value < v {
        var newLeft := delete(left, value);
        res := Node(newLeft, v, right);
      } else if value > v {
        var newRight := delete(right, value);
        res := Node(left, v, newRight);
      } else {
        // Found the node to delete
        if left == Empty {
          res := right;
        } else if right == Empty {
          res := left;
        } else {
          // Node has two children - find inorder successor
          var successor := findMin(right);
          var newRight := delete(right, successor);
          res := Node(left, successor, newRight);
        }
      }
  }
}

method findMin(tree: Tree) returns (min: int)
  requires tree != Empty
{
  match tree {
    case Node(Empty, v, _) => min := v;
    case Node(left, _, _) => min := findMin(left);
  }
}