// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn isPath(paths: Seq<TreeNode>, root: TreeNode) -> bool {
    if paths.len() == 0 then false else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => if paths.len() == 1 then root == paths[0] else root == paths[0] and (isPath(paths[1..], left) or isPath(paths[1..], right))
}

fn hasPathSum(root: TreeNode, targetSum: int) -> (b: bool)
    ensures b ==> exists p: seq<TreeNode> :: isPath(p, root) and pathSum(p) == targetSum
{
}

}