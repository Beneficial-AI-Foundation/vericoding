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


/* code modified by LLM (iteration 1): Added helper lemma to establish path sum properties */
lemma pathSumLemma(root: TreeNode, p: seq<TreeNode>)
  requires |p| > 0 && p[0] == root
  requires root.Cons?
  ensures pathSum(p) == root.val + pathSum(p[1..])
{
  // This follows directly from the definition of pathSum
}

/* code modified by LLM (iteration 1): Added helper lemma to establish path validity properties */
lemma pathValidityLemma(root: TreeNode, p: seq<TreeNode>, child: TreeNode)
  requires |p| > 0 && p[0] == root && root.Cons?
  requires isPath(p[1..], child)
  requires child == root.left || child == root.right
  ensures isPath(p, root)
{
  // This follows directly from the definition of isPath
}

//IMPL hasPathSum

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
  ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
  match root {
    case Nil => 
      b := false;
    case Cons(val, left, right) =>
      /* code modified by LLM (iteration 1): Added check for negative target sum since pathSum returns nat */
      if targetSum < 0 {
        b := false;
      } else if left == Nil && right == Nil {
        // Leaf node
        /* code modified by LLM (iteration 1): Fixed comparison to use nat values directly */
        if val == targetSum {
          /* code modified by LLM (iteration 1): Added assertion to establish witness path for leaf node */
          assert isPath([root], root);
          assert pathSum([root]) == val;
          b := true;
        } else {
          b := false;
        }
      } else {
        var hasLeft := false;
        var hasRight := false;
        
        /* code modified by LLM (iteration 1): Fixed arithmetic and added bounds check */
        if left != Nil && targetSum >= val {
          hasLeft := hasPathSum(left, targetSum - val);
        }
        
        if right != Nil && targetSum >= val {
          hasRight := hasPathSum(right, targetSum - val);
        }
        
        /* code modified by LLM (iteration 1): Added assertions to establish witness paths from recursive calls */
        if hasLeft {
          assert exists p: seq<TreeNode> :: isPath(p, left) && pathSum(p) == targetSum - val;
          var p :| isPath(p, left) && pathSum(p) == targetSum - val;
          var fullPath := [root] + p;
          pathValidityLemma(root, fullPath, left);
          pathSumLemma(root, fullPath);
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == targetSum;
        }
        
        if hasRight {
          assert exists p: seq<TreeNode> :: isPath(p, right) && pathSum(p) == targetSum - val;
          var p :| isPath(p, right) && pathSum(p) == targetSum - val;
          var fullPath := [root] + p;
          pathValidityLemma(root, fullPath, right);
          pathSumLemma(root, fullPath);
          assert isPath(fullPath, root);
          assert pathSum(fullPath) == targetSum;
        }
        
        b := hasLeft || hasRight;
      }
  }
}