datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

predicate BinarySearchTree(tree: Tree)
  decreases tree
{
  match tree
  case Empty => true
  case Node(_,_,_) =>
    (tree.left == Empty || tree.left.value < tree.value)
    && (tree.right == Empty || tree.right.value > tree.value)
    && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
    && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
}

predicate maxValue(tree: Tree, max: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

predicate minValue(tree: Tree, min: int)
  decreases tree
{
  match tree
  case Empty => true
  case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

// <vc-helpers>
function insertRecursionFunc(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) => 
    if value < v then
      Node(insertRecursionFunc(left, value), v, right)
    else if value > v then
      Node(left, v, insertRecursionFunc(right, value))
    else
      tree
}

lemma preservesMaxValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, x) && x > value
  ensures match tree
    case Empty => maxValue(Node(Empty, value, Empty), x)
    case Node(left, v, right) => 
      if value < v then maxValue(Node(insertRecursionFunc(left, value), v, right), x)
      else if value > v then maxValue(Node(left, v, insertRecursionFunc(right, value)), x)
      else maxValue(tree, x)
  decreases tree
{
  match tree {
    case Empty => {}
    case Node(left, v, right) => {
      if value < v {
        preservesMaxValue(left, value, x);
      } else if value > v {
        preservesMaxValue(right, value, x);
      }
    }
  }
}

lemma preservesMinValue(tree: Tree, value: int, x: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, x) && x < value
  ensures match tree
    case Empty => minValue(Node(Empty, value, Empty), x)
    case Node(left, v, right) => 
      if value < v then minValue(Node(insertRecursionFunc(left, value), v, right), x)
      else if value > v then minValue(Node(left, v, insertRecursionFunc(right, value)), x)
      else minValue(tree, x)
  decreases tree
{
  match tree {
    case Empty => {}
    case Node(left, v, right) => {
      if value < v {
        preservesMinValue(left, value, x);
      } else if value > v {
        preservesMinValue(right, value, x);
      }
    }
  }
}

lemma insertPreservesBST(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(insertRecursionFunc(tree, value))
  decreases tree
{
  match tree {
    case Empty => {}
    case Node(left, v, right) => {
      if value < v {
        insertPreservesBST(left, value);
      } else if value > v {
        insertPreservesBST(right, value);
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
// </vc-spec>
// </vc-spec>

// <vc-code>
method insertRecursionImpl(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  res := insertRecursionFunc(tree, value);
  insertPreservesBST(tree, value);
  
  forall x | minValue(tree, x) && x < value
    ensures minValue(res, x)
  {
    preservesMinValue(tree, value, x);
  }
  
  forall x | maxValue(tree, x) && x > value
    ensures maxValue(res, x)
  {
    preservesMaxValue(tree, value, x);
  }
}
// </vc-code>
