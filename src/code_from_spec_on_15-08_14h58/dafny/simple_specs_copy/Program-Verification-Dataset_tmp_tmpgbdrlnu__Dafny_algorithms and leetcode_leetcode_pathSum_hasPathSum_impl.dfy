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
      if left == Nil && right == Nil {
        // Leaf node
        /* code modified by LLM (iteration 1): Fixed leaf node case with explicit path witness */
        if (val as int) == targetSum && targetSum >= 0 {
          b := true;
          var leafPath := [root];
          assert isPath(leafPath, root);
          assert pathSum(leafPath) == val;
          assert pathSum(leafPath) == targetSum;
        } else {
          b := false;
        }
      } else {
        var leftResult := false;
        var rightResult := false;
        
        /* code modified by LLM (iteration 1): Added proper recursive calls with witness construction */
        if left != Nil && targetSum >= (val as int) {
          leftResult := hasPathSum(left, targetSum - (val as int));
        }
        
        if right != Nil && targetSum >= (val as int) {
          rightResult := hasPathSum(right, targetSum - (val as int));
        }
        
        b := leftResult || rightResult;
        
        /* code modified by LLM (iteration 1): Added explicit path witness construction for recursive cases */
        if b && leftResult {
          // By postcondition of leftResult, there exists p_left such that:
          // isPath(p_left, left) && pathSum(p_left) == targetSum - val
          assert exists p_left: seq<TreeNode> :: isPath(p_left, left) && pathSum(p_left) == (targetSum - (val as int));
          var p_left :| isPath(p_left, left) && pathSum(p_left) == (targetSum - (val as int));
          var fullPath := [root] + p_left;
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == val + pathSum(p_left);
          assert pathSum(fullPath) == val + (targetSum - (val as int));
          assert pathSum(fullPath) == targetSum;
        } else if b && rightResult {
          // By postcondition of rightResult, there exists p_right such that:
          // isPath(p_right, right) && pathSum(p_right) == targetSum - val
          assert exists p_right: seq<TreeNode> :: isPath(p_right, right) && pathSum(p_right) == (targetSum - (val as int));
          var p_right :| isPath(p_right, right) && pathSum(p_right) == (targetSum - (val as int));
          var fullPath := [root] + p_right;
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == val + pathSum(p_right);
          assert pathSum(fullPath) == val + (targetSum - (val as int));
          assert pathSum(fullPath) == targetSum;
        }
      }
  }
}