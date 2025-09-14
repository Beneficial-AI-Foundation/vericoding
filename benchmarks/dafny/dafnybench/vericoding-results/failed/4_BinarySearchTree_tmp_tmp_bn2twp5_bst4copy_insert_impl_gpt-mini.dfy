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

method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma maxValue_increase(t: Tree, x: int, y: int)
  requires maxValue(t, x) && x < y
  ensures  maxValue(t, y)
  decreases t
{
  match t {
    case Empty => {}
    case Node(l, v, r) =>
      // from maxValue(t,x) we have x > v, and x < y, so y > v
      maxValue_increase(l, x, y);
      maxValue_increase(r, x, y);
  }
}

lemma minValue_decrease(t: Tree, x: int, y: int)
  requires minValue(t, x) && y < x
  ensures  minValue(t, y)
  decreases t
{
  match t {
    case Empty => {}
    case Node(l, v, r) =>
      // from minValue(t,x) we have x < v, and y < x, so y < v
      minValue_decrease(l, x, y);
      minValue_decrease(r, x, y);
  }
}

lemma preserve_max_on_insert(t: Tree, bound: int, value: int)
  requires BinarySearchTree(t) && maxValue(t, bound) && value < bound
  ensures  maxValue(insert(t, value), bound)
  decreases t
{
  match t {
    case Empty =>
      var res := insert(t, value);
      // res is Node(Empty, value, Empty); and bound > value by assumption
      // therefore maxValue(res, bound) holds
    case Node(l, v, r) =>
      if value < v {
        // left subtree has maxValue(l, v) from BinarySearchTree(t)
        preserve_max_on_insert(l, v, value);
        // now maxValue(insert(l, value), v) holds; lift it to bound (> v)
        maxValue_increase(insert(l, value), v, bound);
        // also r already satisfies maxValue(r, bound) because maxValue(t, bound) implies for all nodes (including r) bound > node
        // overall, Node(insert(l,value), v, r) satisfies maxValue with bound
      } else if value > v {
        // inserting into right subtree does not affect left subtree values; left already < v < bound
        // need to ensure maxValue(insert(r, value), bound) holds
        preserve_max_on_insert(r, bound, value);
        // left subtree values are < v < bound, so they satisfy maxValue with bound
      } else {
        // value == v, no change; maxValue preserved from t
      }
  }
}

lemma preserve_min_on_insert(t: Tree, bound: int, value: int)
  requires BinarySearchTree(t) && minValue(t, bound) && value > bound
  ensures  minValue(insert(t, value), bound)
  decreases t
{
  match t {
    case Empty =>
      var res := insert(t, value);
      // res is Node(Empty, value, Empty); and bound < value by assumption
      // therefore minValue(res, bound) holds
    case Node(l, v, r) =>
      if value > v {
        // right subtree has minValue(r, v) from BinarySearchTree(t)
        preserve_min_on_insert(r, v, value);
        // now minValue(insert(r, value), v) holds; decrease bound from v to bound (bound < v)
        minValue_decrease(insert(r, value), v, bound);
        // left already satisfies minValue(left, bound)
      } else if value < v {
        // inserting into left subtree does not affect right subtree values; right already > v > bound
        preserve_min_on_insert(l, bound, value);
      } else {
        // value == v, no change; minValue preserved from t
      }
  }
}
// </vc-helpers>

// <vc-spec>
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures BinarySearchTree(res)
// </vc-spec>
// <vc-code>
{
  match tree {
    case Empty =>
      res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if value < v {
        var newLeft := insert(left, value);
        // prove BinarySearchTree(newLeft) and maxValue(newLeft, v)
        preserve_max_on_insert(left, v, value);
        // newLeft is BST by postcondition of insert
        // construct result
        res := Node(newLeft, v, right);
      } else if value > v {
        var newRight := insert(right, value);
        preserve_min_on_insert(right, v, value);
        res := Node(left, v, newRight);
      } else {
        // equal: no change
        res := tree;
      }
  }
}
// </vc-code>

