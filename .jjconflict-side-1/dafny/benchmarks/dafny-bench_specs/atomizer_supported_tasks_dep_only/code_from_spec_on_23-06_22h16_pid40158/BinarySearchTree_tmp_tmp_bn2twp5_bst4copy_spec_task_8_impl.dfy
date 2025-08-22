/* code modified by LLM (iteration 4): added missing Tree datatype definition */
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

//IMPL GetMin
method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures BinarySearchTree(tree) ==> (forall x :: minValue(tree, x) ==> x <= res)
  decreases tree
{
  match tree
  case Node(left, value, right) =>
    if left == Empty then
      res := value;
    else {
      /* code modified by LLM (iteration 4): recursive call to get minimum from left subtree */
      res := GetMin(left);
    }
}

//IMPL GetMax
method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures BinarySearchTree(tree) ==> (forall x :: maxValue(tree, x) ==> x >= res)
  decreases tree
{
  match tree
  case Node(left, value, right) =>
    if right == Empty then
      res := value;
    else {
      /* code modified by LLM (iteration 4): recursive call to get maximum from right subtree */
      res := GetMax(right);
    }
}

//IMPL insert
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
{
  /* code modified by LLM (iteration 4): call insertRecursion with proper BST maintenance */
  res := insertRecursion(tree, value);
}

/* code modified by LLM (iteration 4): added helper lemma for BST property verification */
lemma BSTProperty(tree: Tree, newLeft: Tree, v: int, right: Tree, value: int)
  requires BinarySearchTree(tree)
  requires tree.Node? && tree.left == tree.left && tree.value == v && tree.right == right
  requires BinarySearchTree(newLeft)
  requires value < v
  requires maxValue(newLeft, v)
  requires minValue(right, v)
  ensures BinarySearchTree(Node(newLeft, v, right))
{
}

/* code modified by LLM (iteration 4): added helper lemma for right insertion */
lemma BSTPropertyRight(tree: Tree, left: Tree, v: int, newRight: Tree, value: int)
  requires BinarySearchTree(tree)
  requires tree.Node? && tree.left == left && tree.value == v && tree.right == tree.right
  requires BinarySearchTree(newRight)
  requires value > v
  requires maxValue(left, v)
  requires minValue(newRight, v)
  ensures BinarySearchTree(Node(left, v, newRight))
{
}

//IMPL insertRecursion
method insertRecursion(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures BinarySearchTree(res)
  ensures forall x :: minValue(tree, x) && x < value ==> minValue(res, x)
  ensures forall x :: maxValue(tree, x) && x > value ==> maxValue(res, x)
  decreases tree
{
  match tree
  case Empty => 
    /* code modified by LLM (iteration 4): create new node with empty subtrees */
    res := Node(Empty, value, Empty);
  case Node(left, v, right) =>
    if value < v {
      /* code modified by LLM (iteration 4): insert into left subtree and reconstruct */
      var newLeft := insertRecursion(left, value);
      res := Node(newLeft, v, right);
      /* code modified by LLM (iteration 4): assert BST properties are maintained */
      assert maxValue(newLeft, v);
      assert BinarySearchTree(newLeft);
      assert BinarySearchTree(right);
      assert minValue(right, v);
    } else if value > v {
      /* code modified by LLM (iteration 4): insert into right subtree and reconstruct */
      var newRight := insertRecursion(right, value);
      res := Node(left, v, newRight);
      /* code modified by LLM (iteration 4): assert BST properties are maintained */
      assert minValue(newRight, v);
      assert BinarySearchTree(left);
      assert BinarySearchTree(newRight);
      assert maxValue(left, v);
    } else {
      /* code modified by LLM (iteration 4): value already exists, keep tree unchanged */
      res := tree;
    }
}

/* code modified by LLM (iteration 4): added helper lemma for delete operation BST preservation */
lemma DeletePreservesBST(tree: Tree, newLeft: Tree, v: int, right: Tree)
  requires BinarySearchTree(tree)
  requires tree.Node? && tree.left == tree.left && tree.value == v && tree.right == right
  requires newLeft == Empty || BinarySearchTree(newLeft)
  requires maxValue(newLeft, v)
  requires minValue(right, v)  
  requires BinarySearchTree(right)
  ensures newLeft == Empty || BinarySearchTree(Node(newLeft, v, right))
{
}

//IMPL delete
method delete(tree: Tree, value: int) returns (res: Tree)
  requires BinarySearchTree(tree)
  ensures res == Empty || BinarySearchTree(res)
  decreases tree
{
  match tree
  case Empty => 
    res := Empty;
  case Node(left, v, right) =>
    if value < v {
      /* code modified by LLM (iteration 4): delete from left subtree */
      var newLeft := delete(left, value);
      if newLeft == Empty {
        res := Node(Empty, v, right);
      } else {
        res := Node(newLeft, v, right);
        /* code modified by LLM (iteration 4): assert BST properties maintained */
        assert maxValue(newLeft, v);
        assert minValue(right, v);
      }
    } else if value > v {
      /* code modified by LLM (iteration 4): delete from right subtree */
      var newRight := delete(right, value);
      if newRight == Empty {
        res := Node(left, v, Empty);
      } else {
        res := Node(left, v, newRight);
        /* code modified by LLM (iteration 4): assert BST properties maintained */
        assert maxValue(left, v);
        assert minValue(newRight, v);
      }
    } else {
      /* code modified by LLM (iteration 4): handle node deletion cases */
      if left == Empty {
        res := right;
      } else if right == Empty {
        res := left;
      } else {
        var minRight := GetMin(right);
        var newRight := delete(right, minRight);
        if newRight == Empty {
          res := Node(left, minRight, Empty);
        } else {
          res := Node(left, minRight, newRight);
        }
        /* code modified by LLM (iteration 4): assert replacement maintains BST properties */
        assert maxValue(left, minRight);
        if newRight != Empty {
          assert minValue(newRight, minRight);
        }
      }
    }
}

//IMPL Inorder
method Inorder(tree: Tree)
  decreases tree
{
  match tree
  case Empty => 
    return;
  case Node(left, value, right) =>
    /* code modified by LLM (iteration 4): inorder traversal left-root-right */
    Inorder(left);
    print value, " ";
    Inorder(right);
}

//IMPL Postorder
method Postorder(tree: Tree)
  decreases tree
{
  match tree
  case Empty => 
    return;
  case Node(left, value, right) =>
    /* code modified by LLM (iteration 4): postorder traversal left-right-root */
    Postorder(left);
    Postorder(right);
    print value, " ";
}

//IMPL Main
method Main() {
  /* code modified by LLM (iteration 4): demonstrate BST operations */
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