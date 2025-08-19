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
  /* code modified by LLM (iteration 4): Added stronger postcondition to establish precondition for getWitnessPath */
  ensures b <==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
  match root {
    case Nil => 
      b := false;
      /* code modified by LLM (iteration 4): Added assertion to prove no path exists for Nil */
      assert forall p: seq<TreeNode> :: !isPath(p, Nil);
    case Cons(val, left, right) => {
      /* code modified by LLM (iteration 4): Added check for targetSum being non-negative since TreeNode uses nat values */
      if targetSum < 0 {
        b := false;
        /* code modified by LLM (iteration 4): Added assertion to prove no path can have negative sum */
        assert forall p: seq<TreeNode> :: isPath(p, root) ==> pathSum(p) >= 0;
      } else if val == targetSum {
        /* code modified by LLM (iteration 4): Added assertion to help prove the single-node path satisfies postcondition */
        assert isPath([root], root);
        assert pathSum([root]) == val;
        b := true;
      } else if targetSum > val {
        var leftResult := hasPathSum(left, targetSum - val);
        var rightResult := hasPathSum(right, targetSum - val);
        b := leftResult || rightResult;
        /* code modified by LLM (iteration 4): Added assertions to establish precondition for getWitnessPath */
        if b {
          if leftResult {
            assert exists p: seq<TreeNode> :: isPath(p, left) && pathSum(p) == targetSum - val;
            var leftPath := getWitnessPath(left, targetSum - val);
            var fullPath := [root] + leftPath;
            assert isPath(fullPath, root);
            assert pathSum(fullPath) == val + pathSum(leftPath);
            assert pathSum(fullPath) == targetSum;
          } else {
            assert rightResult;
            assert exists p: seq<TreeNode> :: isPath(p, right) && pathSum(p) == targetSum - val;
            var rightPath := getWitnessPath(right, targetSum - val);
            var fullPath := [root] + rightPath;
            assert isPath(fullPath, root);
            assert pathSum(fullPath) == val + pathSum(rightPath);
            assert pathSum(fullPath) == targetSum;
          }
        }
      } else {
        b := false;
        /* code modified by LLM (iteration 4): Added assertion to prove no valid path exists when targetSum < val */
        assert forall p: seq<TreeNode> :: isPath(p, root) ==> pathSum(p) >= val;
      }
    }
  }
}

/* code modified by LLM (iteration 4): Added helper method to construct witness path instead of using assign-such-that */
method getWitnessPath(root: TreeNode, targetSum: int) returns (p: seq<TreeNode>)
  requires exists path: seq<TreeNode> :: isPath(path, root) && pathSum(path) == targetSum
  ensures isPath(p, root) && pathSum(p) == targetSum
{
  match root {
    case Nil => 
      assert false; // This case should not happen given the precondition
      p := [];
    case Cons(val, left, right) =>
      if val == targetSum {
        p := [root];
      } else if targetSum > val {
        var leftHasPath := hasPathSum(left, targetSum - val);
        if leftHasPath {
          var leftPath := getWitnessPath(left, targetSum - val);
          p := [root] + leftPath;
        } else {
          var rightPath := getWitnessPath(right, targetSum - val);
          p := [root] + rightPath;
        }
      } else {
        assert false; // This case should not happen given the precondition
        p := [];
      }
}