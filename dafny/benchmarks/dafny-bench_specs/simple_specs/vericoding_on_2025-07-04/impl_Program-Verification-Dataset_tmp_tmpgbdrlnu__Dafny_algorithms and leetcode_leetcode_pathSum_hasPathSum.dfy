//ATOM

datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)


//ATOM

function pathSum(paths: seq<TreeNode>): nat {
  if |paths| == 0 then 0 else match paths[0] {
    case Nil => 0
    case Cons(val, left, right) => val + pathSum(paths[1..])
  }
}


//ATOM

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
  if |paths| == 0 then false else match paths[0] {
    case Nil => false
    case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
  }
}


//IMPL 

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
  ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
  match root {
    case Nil => 
      b := false;
    case Cons(val, left, right) =>
      /* code modified by LLM (iteration 1): Fixed type conversion and logic for checking single node path */
      if left == Nil && right == Nil {
        // Leaf node case
        if targetSum >= 0 && val == targetSum {
          b := true;
          assert isPath([root], root);
          assert pathSum([root]) == val;
          return;
        } else {
          b := false;
          return;
        }
      }
      
      /* code modified by LLM (iteration 1): Added bounds check and fixed recursive logic */
      if targetSum < 0 || targetSum < val {
        b := false;
        return;
      }
      
      var newTarget := targetSum - val;
      
      if left != Nil {
        var leftResult := hasPathSum(left, newTarget);
        if leftResult {
          b := true;
          /* code modified by LLM (iteration 1): Added assertion to help verification */
          assert exists p: seq<TreeNode> :: isPath(p, left) && pathSum(p) == newTarget;
          var p :| isPath(p, left) && pathSum(p) == newTarget;
          var fullPath := [root] + p;
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == val + pathSum(p);
          assert pathSum(fullPath) == targetSum;
          return;
        }
      }
      
      if right != Nil {
        var rightResult := hasPathSum(right, newTarget);
        if rightResult {
          b := true;
          /* code modified by LLM (iteration 1): Added assertion to help verification */
          assert exists p: seq<TreeNode> :: isPath(p, right) && pathSum(p) == newTarget;
          var p :| isPath(p, right) && pathSum(p) == newTarget;
          var fullPath := [root] + p;
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == val + pathSum(p);
          assert pathSum(fullPath) == targetSum;
          return;
        }
      }
      
      b := false;
  }
}