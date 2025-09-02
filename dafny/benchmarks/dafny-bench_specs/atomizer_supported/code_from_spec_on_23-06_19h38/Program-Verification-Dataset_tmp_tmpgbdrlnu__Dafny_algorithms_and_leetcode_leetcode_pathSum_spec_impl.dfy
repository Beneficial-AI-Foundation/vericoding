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


//IMPL hasPathSum

method hasPathSum(root: TreeNode, targetSum: int) returns (b: bool) 
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) && pathSum(p) == targetSum
{
    match root {
        case Nil => 
            b := false;
        case Cons(val, left, right) =>
            if left == Nil && right == Nil {
                // Leaf node
                /* code modified by LLM (iteration 1): Fixed type conversion from nat to int and added witness for postcondition */
                if val as int == targetSum && targetSum >= 0 {
                    b := true;
                    // Witness: the path is just this single node
                    assert isPath([root], root);
                    assert pathSum([root]) == val;
                    assert val as int == targetSum;
                } else {
                    b := false;
                }
            } else {
                var leftResult := false;
                var rightResult := false;
                
                /* code modified by LLM (iteration 1): Fixed type conversion and added proper path construction */
                if left != Nil {
                    leftResult := hasPathSum(left, targetSum - val as int);
                }
                
                if right != Nil {
                    rightResult := hasPathSum(right, targetSum - val as int);
                }
                
                b := leftResult || rightResult;
                
                /* code modified by LLM (iteration 1): Added assertions to help verification understand path construction */
                if b {
                    if leftResult {
                        // There exists a path in left subtree
                        assert exists p: seq<TreeNode> :: isPath(p, left) && pathSum(p) == targetSum - val as int;
                        var p :| isPath(p, left) && pathSum(p) == targetSum - val as int;
                        var fullPath := [root] + p;
                        assert isPath(fullPath, root);
                        assert pathSum(fullPath) == val + pathSum(p);
                        assert pathSum(fullPath) as int == val as int + (targetSum - val as int);
                        assert pathSum(fullPath) as int == targetSum;
                    } else if rightResult {
                        // There exists a path in right subtree
                        assert exists p: seq<TreeNode> :: isPath(p, right) && pathSum(p) == targetSum - val as int;
                        var p :| isPath(p, right) && pathSum(p) == targetSum - val as int;
                        var fullPath := [root] + p;
                        assert isPath(fullPath, root);
                        assert pathSum(fullPath) == val + pathSum(p);
                        assert pathSum(fullPath) as int == val as int + (targetSum - val as int);
                        assert pathSum(fullPath) as int == targetSum;
                    }
                }
            }
    }
}


//IMPL Test

method Test() {
}