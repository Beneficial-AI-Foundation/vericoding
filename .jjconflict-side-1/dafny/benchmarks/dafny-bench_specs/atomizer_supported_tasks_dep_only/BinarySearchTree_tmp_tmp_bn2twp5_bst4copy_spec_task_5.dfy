//ATOM_PLACEHOLDER_Tree// ATOM 

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


// SPEC 

method GetMin(tree: Tree) returns (res: int)
{
}


//ATOM_PLACEHOLDER_GetMax

//ATOM_PLACEHOLDER_insert

//ATOM_PLACEHOLDER_insertRecursion

// SPEC 

method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  //ensures BinarySearchTree(res)
  //ensures res != Empty ==> BinarySearchTree(res)
{
}


//ATOM_PLACEHOLDER_Inorder

//ATOM_PLACEHOLDER_Postorder

//ATOM_PLACEHOLDER_Main

