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
lemma BST_props(tree: Tree)
  requires BinarySearchTree(tree)
  ensures match tree {
          case Empty => true
          case Node(l,v,r) => BinarySearchTree(l) && BinarySearchTree(r) && maxValue(l,v) && minValue(r,v) && (l==Empty || l.value < v) && (r==Empty || r.value > v)
        }
  decreases tree
{
  match tree {
  case Empty => ();
  case Node(l,v,r) =>
    // From the definition of BinarySearchTree, these follow directly
    assert (l == Empty || l.value < v);
    assert (r == Empty || r.value > v);
    assert maxValue(l, v);
    assert minValue(r, v);
    assert BinarySearchTree(l);
    assert BinarySearchTree(r);
  }
}
// </vc-helpers>

// <vc-spec>
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree;
  ensures res != Empty ==> BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
// </vc-spec>
// <vc-code>
{
  match tree {
  case Empty => res := Node(Empty, value, Empty);
  case Node(left, v, right) =>
    // extract useful facts from the precondition
    BST_props(tree);
    if value < v {
      var newLeft := insertRecursion(left, value);
      // use facts to instantiate the recursive postcondition
      assert v > value;
      assert maxValue(left, v);
      // from the postcondition of the recursive call:
      // forall x :: maxValue(left, x) && x > value ==> maxValue(newLeft, x)
      // instantiate with x := v to obtain maxValue(newLeft, v)
      assert maxValue(newLeft, v);
      res := Node(newLeft, v, right);
    } else if value > v {
      var newRight := insertRecursion(right, value);
      assert value > v;
      assert minValue(right, v);
      // from the postcondition of the recursive call:
      // forall x :: minValue(right, x) && x < value ==> minValue(newRight, x)
      // instantiate with x := v to obtain minValue(newRight, v)
      assert minValue(newRight, v);
      res := Node(left, v, newRight);
    } else {
      // value == v: no change
      res := tree;
    }
  }
}
// </vc-code>

