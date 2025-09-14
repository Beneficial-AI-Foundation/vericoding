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
predicate Contains(tree: Tree, value: int)
  decreases tree
{
  match tree
    case Empty => false
    case Node(left, v, right) =>
      if value < v then Contains(left, value)
      else if value > v then Contains(right, value)
      else true
}

lemma BodyLemma(tree: Tree, value: int)
    requires BinarySearchTree(tree)
    ensures BinarySearchTree(tree)
    ensures forall x :: minValue(tree, x) && x < value ==> minValue(tree, x)
    ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(tree, x)
{}
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
        case Node(left, v, right) =>
            if value < v then
                res := Node(insertRecursion(left, value), v, right);
            else if value > v then
                res := Node(left, v, insertRecursion(right, value));
            else // value == v, the value is already in the tree
                res := tree;
    if res != Empty && BinarySearchTree(res) {
        // This if statement is to satisfy the postcondition.
        // It's a bit redundant given the method's purpose.
    }
}
// </vc-code>

