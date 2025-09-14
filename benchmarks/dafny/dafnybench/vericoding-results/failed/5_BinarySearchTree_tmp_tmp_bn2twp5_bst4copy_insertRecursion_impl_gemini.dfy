// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Keeping helper lemmas as they may be necessary for verification, despite the primary error being in the code. */
lemma maxValue_root(t:Tree, x:int)
  requires t.Node? && maxValue(t, x)
  ensures t.value < x
{
}

lemma minValue_root(t:Tree, x:int)
  requires t.Node? && minValue(t, x)
  ensures x < t.value
{
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
/* code modified by LLM (iteration 5): Fixed a definite-assignment error by removing an assertion placed before a variable's initialization. */
{
  match tree {
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
}
// </vc-code>
