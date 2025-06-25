datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

spec fn BinarySearchTree(tree: Tree) -> bool
{
  match tree {
    Tree::Empty => true,
    Tree::Node(_, _, _) =>
      (tree.left == Tree::Empty || tree.left.value < tree.value)
      && (tree.right == Tree::Empty || tree.right.value > tree.value)
      && BinarySearchTree(tree.left) && BinarySearchTree(tree.right)
      && minValue(tree.right, tree.value) && maxValue(tree.left, tree.value)
  }
}

spec fn maxValue(tree: Tree, max: int) -> bool
{
  match tree {
    Tree::Empty => true,
    Tree::Node(left, v, right) => (max > v) && maxValue(left, max) && maxValue(right, max)
  }
}

spec fn minValue(tree: Tree, min: int) -> bool
{
  match tree {
    Tree::Empty => true,
    Tree::Node(left, v, right) => (min < v) && minValue(left, min) && minValue(right, min)
  }
}

pub fn GetMin(tree: Tree) -> (res: int)
{
}

pub fn delete(tree: Tree, value: int) -> (res: Tree)
  requires BinarySearchTree(tree)
{
}