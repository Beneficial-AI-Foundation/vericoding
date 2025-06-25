//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL 
method GetMin(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures tree != Empty ==> (forall v :: v in TreeValues(tree) ==> res <= v)
  ensures res in TreeValues(tree)
{
  match tree {
    case Node(left, value, right) =>
      if left == Empty && right == Empty {
        res := value;
      } else if left == Empty {
        var rightMin := GetMin(right);
        res := if value <= rightMin then value else rightMin;
      } else if right == Empty {
        var leftMin := GetMin(left);
        res := if value <= leftMin then value else leftMin;
      } else {
        var leftMin := GetMin(left);
        var rightMin := GetMin(right);
        res := if value <= leftMin && value <= rightMin then value
               else if leftMin <= rightMin then leftMin
               else rightMin;
      }
  }
}

function TreeValues(tree: Tree): set<int>
{
  match tree {
    case Empty => {}
    case Node(left, value, right) => TreeValues(left) + {value} + TreeValues(right)
  }
}