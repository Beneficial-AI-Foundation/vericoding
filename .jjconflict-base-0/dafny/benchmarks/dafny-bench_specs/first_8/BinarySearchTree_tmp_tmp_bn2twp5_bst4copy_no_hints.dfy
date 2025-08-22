//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)
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

//SPEC
// NOTE: requires, ensures added by hand
method GetMin(tree: Tree) returns (res: int)
  requires BinarySearchTree(tree)
  ensures minValue(tree, res)
{}

//SPEC
// NOTE: requires, ensures added by hand
method GetMax(tree: Tree) returns (res: int)
  requires BinarySearchTree(tree)
  ensures maxValue(tree, res)
{}

//SPEC
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{}

//SPEC
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res != Empty ==> BinarySearchTree(res) // NOTE: requires, ensures added by hand
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x) // NOTE: requires, ensures added by hand
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x) // NOTE: requires, ensures added by hand
{}

//SPEC
// NOTE: uncommented ensures
method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  ensures res != Empty ==> BinarySearchTree(res)
{}

//SPEC
method deleteRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  ensures res != Empty ==> BinarySearchTree(res)
  {}

//ATOM
method Inorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Inorder(tree.left);
      print tree.value, ", ";
      Inorder(tree.right);
  }
}
//ATOM
method Postorder(tree: Tree)
{
  match tree {
    case Empty =>
    case Node(left, value, right) =>
      Postorder(tree.left);
      Postorder(tree.right);
      print tree.value, ", ";
  }
}

//SPEC
method Main() {
  var tree := insert(Empty, 3);
  var u := insert(tree, 2);

  u := insert(u, 7);
  u := insert(u, 6);
  u := insert(u, 9);


  print "This is Inorder: ";
  Inorder(u);
  print "\n";
  //u := delete (u, 1);

  print "This is Postorder: ";
  Postorder(u);
  print "\n";

  print "tree before delete: ", u, "\n";

  u := delete(u, 7);
  print "tree after delete: ", u, "\n";

  print "This is Inorder: ";
  Inorder(u);

  print "\n";
  print "This is Postorder: ";
  Postorder(u);

  // var res := GetMin(u);
  // var max := GetMax(u);
  // print "this is max: ", max;
  //print "this is res: ", res;

  //print u;
}
