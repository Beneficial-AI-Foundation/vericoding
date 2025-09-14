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
lemma RootLessFromMaxValue(t: Tree, m: int)
  requires maxValue(t, m)
  ensures t == Empty || t.value < m
  decreases t
{
  match t
  case Empty =>
  case Node(_, v, _) =>
    assert m > v;
}

lemma RootGreaterFromMinValue(t: Tree, m: int)
  requires minValue(t, m)
  ensures t == Empty || t.value > m
  decreases t
{
  match t
  case Empty =>
  case Node(_, v, _) =>
    assert m < v;
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
  match tree
  case Empty =>
    res := Node(Empty, value, Empty);
  case Node(l, v, r) =>
    if value < v {
      var l' := insertRecursion(l, value);

      assert BinarySearchTree(tree);
      assert BinarySearchTree(r);
      assert maxValue(l, v);
      assert minValue(r, v);
      assert r == Empty || r.value > v;

      assert v > value;
      assert maxValue(l', v);
      RootLessFromMaxValue(l', v);

      if l' != Empty {
        assert BinarySearchTree(l');
      }

      res := Node(l', v, r);
      assert l' == Empty || l'.value < v;
      assert minValue(r, v);
      assert maxValue(l', v);
      assert BinarySearchTree(r);
    } else if value > v {
      var r' := insertRecursion(r, value);

      assert BinarySearchTree(tree);
      assert BinarySearchTree(l);
      assert maxValue(l, v);
      assert l == Empty || l.value < v;

      assert minValue(r, v);
      assert v < value;
      assert minValue(r', v);
      RootGreaterFromMinValue(r', v);

      if r' != Empty {
        assert BinarySearchTree(r');
      }

      res := Node(l, v, r');
      assert r' == Empty || r'.value > v;
      assert maxValue(l, v);
      assert minValue(r', v);
      assert BinarySearchTree(l);
    } else {
      res := tree;
    }
}
// </vc-code>

