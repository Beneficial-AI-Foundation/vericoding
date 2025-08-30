//https://leetcode.com/problems/path-sum
/**
// SPEC 

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
}
;
 */

// ATOM 

datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)
// ATOM 

function TreeSeq(root: TreeNode): seq<TreeNode> {
    match root {
        case Nil => [Nil]
        case Cons(val, left, right) => [root]+TreeSeq(left)+TreeSeq(right)
    }
}


// ATOM 

function TreeSet(root: TreeNode): set<TreeNode> {
    match root {
        case Nil => {Nil}
        case Cons(val, left, right) => TreeSet(left)+{root}+TreeSet(right)
    }
}


// ATOM 

predicate isPath(paths: seq<TreeNode>, root: TreeNode) {
    if |paths| == 0 then false else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}


// ATOM 

function pathSum(paths: seq<TreeNode>): nat {
    if |paths| == 0 then 0 else match paths[0] {
        case Nil => 0
        case Cons(val, left, right) => val + pathSum(paths[1..])
    }
}


// SPEC 

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
}


// SPEC 

method Test() {
}








