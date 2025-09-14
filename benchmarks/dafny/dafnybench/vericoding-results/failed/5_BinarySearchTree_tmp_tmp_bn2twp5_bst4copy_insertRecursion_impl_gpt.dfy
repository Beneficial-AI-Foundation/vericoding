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
lemma maxValueNonEmptyImpliesRootLess(t: Tree, m: int)
  ensures t != Empty && maxValue(t, m) ==> t.value < m
  decreases t
{
  match t
  case Empty =>
  case Node(l, v, r) =>
    if maxValue(t, m) {
      assert m > v;
      assert t.value == v;
      assert t.value < m;
    }
}

lemma minValueNonEmptyImpliesRootGreater(t: Tree, m: int)
  ensures t != Empty && minValue(t, m) ==> m < t.value
  decreases t
{
  match t
  case Empty =>
  case Node(l, v, r) =>
    if minValue(t, m) {
      assert m < v;
      assert t.value == v;
      assert m < t.value;
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
  match tree
  case Empty =>
    res := Node(Empty, value, Empty);
  case Node(l, v, r) =>
    if value < v {
      var nl := insertRecursion(l, value);
      assert BinarySearchTree(tree);
      assert BinarySearchTree(l);
      assert BinarySearchTree(r);
      assert maxValue(l, v);
      assert minValue(r, v);
      assert r == Empty || r.value > v;

      assert v > value;
      assert maxValue(nl, v);

      if nl == Empty {
        assert BinarySearchTree(nl);
      } else {
        assert BinarySearchTree(nl);
        maxValueNonEmptyImpliesRootLess(nl, v);
        assert nl.value < v;
      }

      res := Node(nl, v, r);
    } else if value > v {
      var nr := insertRecursion(r, value);
      assert BinarySearchTree(tree);
      assert BinarySearchTree(l);
      assert BinarySearchTree(r);
      assert maxValue(l, v);
      assert l == Empty || l.value < v;
      assert minValue(r, v);

      assert v < value;
      assert minValue(nr, v);

      if nr == Empty {
        assert BinarySearchTree(nr);
      } else {
        assert BinarySearchTree(nr);
        minValueNonEmptyImpliesRootGreater(nr, v);
        assert nr.value > v;
      }

      res := Node(l, v, nr);
    } else {
      res := tree;
    }
}
// </vc-code>

