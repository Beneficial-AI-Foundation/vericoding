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


// SPEC

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
  ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
}