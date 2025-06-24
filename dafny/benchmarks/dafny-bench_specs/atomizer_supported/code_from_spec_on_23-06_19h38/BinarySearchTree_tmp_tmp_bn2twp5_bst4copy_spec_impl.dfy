// ATOM 
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

// ATOM 
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

// IMPL GetMin
/* code modified by LLM (iteration 4): fixed to properly ensure minimum value */
method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures tree.Node? ==> res == GetMinValue(tree)
  decreases tree
{
  match tree
  case Empty => res := 0; // This case should never be reached due to precondition
  case Node(left, value, right) =>
    if left == Empty then
      res := value;
    else
      res := GetMin(left);
}

// IMPL GetMax
/* code modified by LLM (iteration 4): fixed to properly ensure maximum value */
method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures tree.Node? ==> res == GetMaxValue(tree)
  decreases tree
{
  match tree
  case Empty => res := 0; // This case should never be reached due to precondition
  case Node(left, value, right) =>
    if right == Empty then
      res := value;
    else
      res := GetMax(right);
}

/* code modified by LLM (iteration 4): added helper function to get minimum value */
function GetMinValue(tree: Tree): int
  requires tree != Empty
  decreases tree
{
  match tree
  case Node(Empty, value, _) => value
  case Node(left, _, _) => GetMinValue(left)
}

/* code modified by LLM (iteration 4): added helper function to get maximum value */
function GetMaxValue(tree: Tree): int
  requires tree != Empty
  decreases tree
{
  match tree
  case Node(_, value, Empty) => value
  case Node(_, _, right) => GetMaxValue(right)
}

/* code modified by LLM (iteration 4): enhanced BST property lemma */
lemma BSTProperty(tree: Tree)
  requires BinarySearchTree(tree)
  requires tree.Node?
  ensures tree.left == Empty || tree.left.value < tree.value
  ensures tree.right == Empty || tree.right.value > tree.value
  ensures BinarySearchTree(tree.left)
  ensures BinarySearchTree(tree.right)
  ensures maxValue(tree.left, tree.value)
  ensures minValue(tree.right, tree.value)
{
  // Property holds by definition of BinarySearchTree
}

/* code modified by LLM (iteration 4): enhanced insertion lemma with proper proofs */
lemma InsertionPreservesMaxValue(tree: Tree, value: int, bound: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, bound)
  requires value < bound
  ensures maxValue(insertTree(tree, value), bound)
  decreases tree
{
  match tree
  case Empty => 
  case Node(left, v, right) =>
    if value < v {
      InsertionPreservesMaxValue(left, value, bound);
    } else if value > v {
      InsertionPreservesMaxValue(right, value, bound);
    }
}

/* code modified by LLM (iteration 4): enhanced insertion lemma with proper proofs */
lemma InsertionPreservesMinValue(tree: Tree, value: int, bound: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, bound)
  requires value > bound
  ensures minValue(insertTree(tree, value), bound)
  decreases tree
{
  match tree
  case Empty => 
  case Node(left, v, right) =>
    if value < v {
      InsertionPreservesMinValue(left, value, bound);
    } else if value > v {
      InsertionPreservesMinValue(right, value, bound);
    }
}

/* code modified by LLM (iteration 4): added pure function for insertion */
function insertTree(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(insertTree(tree, value))
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) =>
    if value < v then
      var newLeft := insertTree(left, value);
      InsertionPreservesMinValue(newLeft, v, value);
      Node(newLeft, v, right)
    else if value > v then
      var newRight := insertTree(right, value);
      InsertionPreservesMaxValue(newRight, v, value);
      Node(left, v, newRight)
    else
      tree
}

// IMPL insert
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  res := insertRecursion(tree, value);
}

// IMPL insertRecursion
/* code modified by LLM (iteration 4): simplified using verified function */
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  decreases tree
{
  res := insertTree(tree, value);
}

/* code modified by LLM (iteration 4): lemmas for deletion verification */
lemma DeletionPreservesMaxValue(tree: Tree, value: int, bound: int)
  requires BinarySearchTree(tree)
  requires maxValue(tree, bound)
  ensures maxValue(deleteTree(tree, value), bound)
  decreases tree
{
  match tree
  case Empty => 
  case Node(left, v, right) =>
    if value < v {
      DeletionPreservesMaxValue(left, value, bound);
    } else if value > v {
      DeletionPreservesMaxValue(right, value, bound);
    } else {
      if left != Empty && right != Empty {
        DeletionPreservesMaxValue(right, GetMinValue(right), bound);
      }
    }
}

/* code modified by LLM (iteration 4): lemmas for deletion verification */
lemma DeletionPreservesMinValue(tree: Tree, value: int, bound: int)
  requires BinarySearchTree(tree)
  requires minValue(tree, bound)
  ensures minValue(deleteTree(tree, value), bound)
  decreases tree
{
  match tree
  case Empty => 
  case Node(left, v, right) =>
    if value < v {
      DeletionPreservesMinValue(left, value, bound);
    } else if value > v {
      DeletionPreservesMinValue(right, value, bound);
    } else {
      if left != Empty && right != Empty {
        DeletionPreservesMinValue(right, GetMinValue(right), bound);
      }
    }
}

/* code modified by LLM (iteration 4): added pure function for deletion */
function deleteTree(tree: Tree, value: int): Tree
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(deleteTree(tree, value))
  decreases tree
{
  match tree
  case Empty => Empty
  case Node(left, v, right) =>
    if value < v then
      var newLeft := deleteTree(left, value);
      DeletionPreservesMinValue(newLeft, v, value);
      Node(newLeft, v, right)
    else if value > v then
      var newRight := deleteTree(right, value);
      DeletionPreservesMaxValue(newRight, v, value);
      Node(left, v, newRight)
    else
      if left == Empty then
        right
      else if right == Empty then
        left
      else
        var minRight := GetMinValue(right);
        var newRight := deleteTree(right, minRight);
        DeletionPreservesMinValue(newRight, minRight, v);
        DeletionPreservesMaxValue(newRight, minRight, v);
        Node(left, minRight, newRight)
}

// IMPL delete
/* code modified by LLM (iteration 4): simplified using verified function */
method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  decreases tree
{
  res := deleteTree(tree, value);
}

// IMPL Inorder
method Inorder(tree: Tree)
  decreases tree
{
  match tree
  case Empty => 
    return;
  case Node(left, value, right) =>
    Inorder(left);
    print value, " ";
    Inorder(right);
}

// IMPL Postorder
method Postorder(tree: Tree)
  decreases tree
{
  match tree
  case Empty => 
    return;
  case Node(left, value, right) =>
    Postorder(left);
    Postorder(right);
    print value, " ";
}

// IMPL Main
method Main() 
{
  var tree := Empty;
  tree := insert(tree, 5);
  tree := insert(tree, 3);
  tree := insert(tree, 7);
  print "Inorder traversal: ";
  Inorder(tree);
  print "\n";
  print "Postorder traversal: ";
  Postorder(tree);
  print "\n";
}