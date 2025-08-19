//ATOM
datatype Tree = Empty | Node(left: Tree, value: int, right: Tree)

//IMPL GetMax
method GetMax(tree: Tree) returns (res: int)
  requires tree != Empty
  ensures tree != Empty ==> (forall x :: x in TreeValues(tree) ==> x <= res)
  ensures tree != Empty ==> res in TreeValues(tree)
{
  /* code modified by LLM (iteration 1): Added complete implementation with proper tree traversal */
  match tree {
    case Empty => 
      // This case is excluded by the precondition
      assert false;
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

/* code modified by LLM (iteration 1): Added helper function to define tree values for specification */
function TreeValues(tree: Tree): set<int>
{
  match tree {
    case Empty => {}
    case Node(left, value, right) => {value} + TreeValues(left) + TreeValues(right)
  }
}