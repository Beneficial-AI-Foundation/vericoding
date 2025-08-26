lemma minValuePreserved(tree: Tree, newTree: Tree, min: int, insertedValue: int)
  requires BinarySearchTree(tree)
  requires BinarySearchTree(newTree)
  requires minValue(tree, min)
  requires min < insertedValue
  requires newTree == insertHelper(tree, insertedValue)
  ensures minValue(newTree, min)
  decreases tree
{
  match tree {
    case Empty => 
      assert newTree == Node(Empty, insertedValue, Empty);
      assert min < insertedValue;
    case Node(left, v, right) =>
      if insertedValue == v {
        assert newTree == tree;
      } else if insertedValue < v {
        var newLeft := insertHelper(left, insertedValue);
        assert newTree == Node(newLeft, v, right);
        minValuePreserved(left, newLeft, min, insertedValue);
      } else {
        var newRight := insertHelper(right, insertedValue);
        assert newTree == Node(left, v, newRight);
        minValuePreserved(right, newRight, min, insertedValue);
      }
  }
}

lemma maxValuePreserved(tree: Tree, newTree: Tree, max: int, insertedValue: int)
  requires BinarySearchTree(tree)
  requires BinarySearchTree(newTree)
  requires maxValue(tree, max)
  requires max > insertedValue
  requires newTree == insertHelper(tree, insertedValue)
  ensures maxValue(newTree, max)
  decreases tree
{
  match tree {
    case Empty => 
      assert newTree == Node(Empty, insertedValue, Empty);
      assert max > insertedValue;
    case Node(left, v, right) =>
      if insertedValue == v {
        assert newTree == tree;
      } else if insertedValue < v {
        var newLeft := insertHelper(left, insertedValue);
        assert newTree == Node(newLeft, v, right);
        maxValuePreserved(left, newLeft, max, insertedValue);
      } else {
        var newRight := insertHelper(right, insertedValue);
        assert newTree == Node(left, v, newRight);
        maxValuePreserved(right, newRight, max, insertedValue);
      }
  }
}

lemma insertPreservesBST(tree: Tree, value: int, result: Tree)
  requires BinarySearchTree(tree)
  requires result == insertHelper(tree, value)
  ensures BinarySearchTree(result)
  decreases tree
{
  match tree {
    case Empty => 
      assert result == Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if value == v {
        assert result == tree;
      } else if value < v {
        var newLeft := insertHelper(left, value);
        insertPreservesBST(left, value, newLeft);
        assert result == Node(newLeft, v, right);
        assert BinarySearchTree(newLeft);
        assert minValue(right, v);
        assert maxValue(newLeft, v);
      } else {
        var newRight := insertHelper(right, value);
        insertPreservesBST(right, value, newRight);
        assert result == Node(left, v, newRight);
        assert BinarySearchTree(newRight);
        assert maxValue(left, v);
        assert minValue(newRight, v);
      }
  }
}

function insertHelper(tree: Tree, value: int): Tree
  decreases tree
{
  match tree {
    case Empty => Node(Empty, value, Empty)
    case Node(left, v, right) =>
      if value == v then tree
      else if value < v then Node(insertHelper(left, value), v, right)
      else Node(left, v, insertHelper(right, value))
  }
}

// <vc-spec>
method insert(tree: Tree, value : int) returns (res: Tree)
  requires BinarySearchTree(tree)
  decreases tree
  ensures BinarySearchTree(res)
// </vc-spec>
// <vc-code>
{
  match tree {
    case Empty => 
      res := Node(Empty, value, Empty);
    case Node(left, v, right) =>
      if value == v {
        res := tree;
      } else if value < v {
        var newLeft := insert(left, value);
        res := Node(newLeft, v, right);
        // Use the helper lemma to establish maxValue property
        insertPreservesBST(left, value, newLeft);
        assert BinarySearchTree(newLeft);
        assert minValue(right, v);
        assert maxValue(newLeft, v);
      } else {
        var newRight := insert(right, value);
        res := Node(left, v, newRight);
        // Use the helper lemma to establish minValue property  
        insertPreservesBST(right, value, newRight);
        assert BinarySearchTree(newRight);
        assert maxValue(left, v);
        assert minValue(newRight, v);
      }
  }
}
// </vc-code>