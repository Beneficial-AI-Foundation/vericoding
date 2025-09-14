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
predicate Contains(tree: Tree, value: int)
{
  match tree
  case Empty => false
  case Node(left, v, right) =>
    v == value || (value < v && Contains(left, value)) || (value > v && Contains(right, value))
}

lemma LemmaValueStaysInTreeWhenInsertedIntoEmpty(value: int)
  ensures BinarySearchTree(Node(Empty, value, Empty))
  ensures Contains(Node(Empty, value, Empty), value)
{
  assert Node(Empty, value, Empty).left == Empty;
  assert Node(Empty, value, Empty).right == Empty;
  assert BinarySearchTree(Empty);
}

lemma BinarySearchTreePreservesProperties(tree: Tree)
  requires BinarySearchTree(tree)
  ensures (tree.left != Empty ==> tree.left.value < tree.value)
  ensures (tree.right != Empty ==> tree.right.value > tree.value)
  ensures (tree.left != Empty ==> maxValue(tree.left, tree.value))
  ensures (tree.right != Empty ==> minValue(tree.right, tree.value))
{}

function InsertRecursion(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  decreases tree
{
  if tree == Empty then
    Node(Empty, value, Empty)
  else if value < tree.value then
    Node(InsertRecursion(tree.left, value), tree.value, tree.right)
  else if value > tree.value then
    Node(tree.left, tree.value, InsertRecursion(tree.right, value))
  else
    tree
}

lemma LemmaInsertRecursionPreservesContainment(tree: Tree, value: int, inserted_value: int)
  requires BinarySearchTree(tree)
  requires !Contains(tree, inserted_value)
  ensures Contains(InsertRecursion(tree, inserted_value), inserted_value)
  ensures forall v :: v != inserted_value && Contains(tree, v) ==> Contains(InsertRecursion(tree, inserted_value), v)
{}

lemma BinarySearchTreeInsertionPreservesProperties(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(InsertRecursion(tree, value))
{
  if tree == Empty {
    LemmaValueStaysInTreeWhenInsertedIntoEmpty(value);
  } else if value < tree.value {
    BinarySearchTreeInsertionPreservesProperties(tree.left, value);
    BinarySearchTreePreservesProperties(tree);
    assert (tree.left == Empty || tree.left.value < tree.value);
    assert (tree.right == Empty || tree.right.value > tree.value);
    assert BinarySearchTree(tree.left);
    assert BinarySearchTree(tree.right);
    assert minValue(tree.right, tree.value);
    assert maxValue(tree.left, tree.value);
    var newLeft := InsertRecursion(tree.left, value);
    if newLeft.value == value {
      if newLeft.value < tree.value { } else { assert false; }
    }
    assert BinarySearchTree(newLeft);
    assert BinarySearchTree(Node(newLeft, tree.value, tree.right));
  } else if value > tree.value {
    BinarySearchTreeInsertionPreservesProperties(tree.right, value);
    BinarySearchTreePreservesProperties(tree);
    assert (tree.left == Empty || tree.left.value < tree.value);
    assert (tree.right == Empty || tree.right.value > tree.value);
    assert BinarySearchTree(tree.left);
    assert BinarySearchTree(tree.right);
    assert minValue(tree.right, tree.value);
    assert maxValue(tree.left, tree.value);
    var newRight := InsertRecursion(tree.right, value);
    if newRight.value == value {
      if newRight.value > tree.value { } else { assert false; }
    }
    assert BinarySearchTree(newRight);
    assert BinarySearchTree(Node(tree.left, tree.value, newRight));
  } else {
    // Value already exists, tree remains a BST
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
    if tree == Empty {
        LemmaValueStaysInTreeWhenInsertedIntoEmpty(value);
        return Node(Empty, value, Empty);
    } else if value < tree.value {
        var newLeft := insert(tree.left, value);
        if newLeft.value == value {
          assert newLeft.value < tree.value;
        }
        BinarySearchTreeInsertionPreservesProperties(tree.left, value); // Call the helper lemma here
        return Node(newLeft, tree.value, tree.right);
    } else if value > tree.value {
        var newRight := insert(tree.right, value);
        if newRight.value == value {
          assert newRight.value > tree.value;
        }
        BinarySearchTreeInsertionPreservesProperties(tree.right, value); // Call the helper lemma here
        return Node(tree.left, tree.value, newRight);
    } else {
        // Value already exists, return the original tree
        return tree;
    }
}
// </vc-code>

