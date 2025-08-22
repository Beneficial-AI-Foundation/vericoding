//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)


//ATOM

method insert(tree: Tree, value : int) returns (res: Tree)
 requires BinarySearchTree(tree)
 ensures BinarySearchTree(res)
{
  res := Empty;
  assume BinarySearchTree(res);
  return res;
}


//ATOM

predicate minValue(tree: Tree, min: int)
{
 match tree
 case Empty => true
 case Node(left,v,right) => (min < v) && minValue(left, min) && minValue(right, min)
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

method GetMin(tree: Tree) returns (res: int)
{
  res := 0;
  return res;
}


//ATOM

method Inorder(tree: Tree)
{
}


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

method GetMax(tree: Tree) returns (res: int){
  res := 0;
  return res;
}


//ATOM

method delete(tree: Tree, value: int) returns (res: Tree)
 requires BinarySearchTree(tree)
 //ensures BinarySearchTree(res)
 //ensures res != Empty ==> BinarySearchTree(res)
{
  res := Empty;
  return res;
}


//ATOM

method Postorder(tree: Tree)
{
}


// SPEC

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
