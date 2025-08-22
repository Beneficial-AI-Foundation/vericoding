//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//ATOM
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures res != Empty ==> BinarySearchTree(res)
 ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
 ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
{
  res := Empty;
  assume res != Empty ==> BinarySearchTree(res);
  assume forall x :: minValue(tree, x) && x < value ==> minValue(res, x);
  assume forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x);
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
predicate maxValue(tree: Tree, max: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (max > v) && maxValue(left, max) && maxValue(right, max)
}

//ATOM
predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
}

//IMPL insert
/* code modified by LLM (iteration 1): Added helper function for BST insertion */
function insertHelper(tree: Tree, value: int): Tree
  decreases tree
{
  match tree
  case Empty => Node(Empty, value, Empty)
  case Node(left, v, right) =>
    if value < v then
      Node(insertHelper(left, value), v, right)
    else if value > v then
      Node(left, v, insertHelper(right, value))
    else
      tree
}

/* code modified by LLM (iteration 1): Added lemma to prove BST property preservation */
lemma InsertPreservesBST(tree: Tree, value: int)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(insertHelper(tree, value))
  decreases tree
{
  match tree
  case Empty => {
    // Base case: inserting into empty tree creates valid BST
  }
  case Node(left, v, right) => {
    if value < v {
      InsertPreservesBST(left, value);
      var newLeft := insertHelper(left, value);
      // Prove that the new tree maintains BST properties
      assert BinarySearchTree(newLeft);
      assert maxValue(newLeft, v);
    } else if value > v {
      InsertPreservesBST(right, value);
      var newRight := insertHelper(right, value);
      // Prove that the new tree maintains BST properties
      assert BinarySearchTree(newRight);
      assert minValue(newRight, v);
    }
  }
}

method insert(tree: Tree, value : int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures BinarySearchTree(res)
{
  /* code modified by LLM (iteration 1): Call helper lemma and use helper function */
  InsertPreservesBST(tree, value);
  res := insertHelper(tree, value);
}