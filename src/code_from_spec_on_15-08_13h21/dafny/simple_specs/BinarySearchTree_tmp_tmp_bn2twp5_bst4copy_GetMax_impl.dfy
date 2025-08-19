//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
{
  match tree {
    case Node(left, value, right) =>
      res := value;
      if left != Empty {
        var leftMax := GetMax(left);
        if leftMax > res {
          res := leftMax;
        }
      }
      if right != Empty {
        var rightMax := GetMax(right);
        if rightMax > res {
          res := rightMax;
        }
      }
  }
}