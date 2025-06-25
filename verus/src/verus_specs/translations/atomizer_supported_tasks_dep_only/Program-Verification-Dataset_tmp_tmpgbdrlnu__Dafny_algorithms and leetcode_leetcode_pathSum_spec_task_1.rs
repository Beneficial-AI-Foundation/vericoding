use vstd::prelude::*;

verus! {

spec fn is_path(paths: Seq<TreeNode>, root: TreeNode) -> bool {
    if paths.len() == 0 { 
        false 
    } else { 
        match paths[0] {
            TreeNode::Nil => false,
            TreeNode::Cons(val, left, right) => {
                if paths.len() == 1 { 
                    root == paths[0] 
                } else { 
                    root == paths[0] && (is_path(paths.subrange(1, paths.len() as int), left) || is_path(paths.subrange(1, paths.len() as int), right))
                }
            }
        }
    }
}

spec fn path_sum(paths: Seq<TreeNode>) -> nat {
    if paths.len() == 0 { 
        0 
    } else { 
        match paths[0] {
            TreeNode::Nil => 0,
            TreeNode::Cons(val, left, right) => val + path_sum(paths.subrange(1, paths.len() as int))
        }
    }
}

pub fn has_path_sum(root: TreeNode, target_sum: int) -> (b: bool)
    ensures(b ==> exists|p: Seq<TreeNode>| is_path(p, root) && path_sum(p) == target_sum)
{
}

}