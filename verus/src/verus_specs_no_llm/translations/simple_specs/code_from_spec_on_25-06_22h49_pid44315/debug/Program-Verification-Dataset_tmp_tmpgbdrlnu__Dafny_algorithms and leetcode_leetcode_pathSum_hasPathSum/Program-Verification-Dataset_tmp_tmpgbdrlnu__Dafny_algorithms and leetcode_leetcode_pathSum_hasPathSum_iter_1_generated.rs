use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq)]
enum TreeNode {
    Nil,
    Cons(int, Box<TreeNode>, Box<TreeNode>),
}

fn main() {
}

spec fn isPath(paths: Seq<TreeNode>, root: TreeNode) -> bool {
    if paths.len() == 0 then 
        false 
    else match paths.spec_index(0) {
        TreeNode::Nil => false,
        TreeNode::Cons(val, left, right) => 
            if paths.len() == 1 then 
                root == paths.spec_index(0) && root.is_leaf()
            else 
                root == paths.spec_index(0) && 
                (isPath(paths.subrange(1, paths.len() as int), *left) || 
                 isPath(paths.subrange(1, paths.len() as int), *right))
    }
}

spec fn pathSum(paths: Seq<TreeNode>) -> int 
    decreases paths.len()
{
    if paths.len() == 0 then 
        0 
    else match paths.spec_index(0) {
        TreeNode::Nil => 0,
        TreeNode::Cons(val, _, _) => val + pathSum(paths.subrange(1, paths.len() as int))
    }
}

impl TreeNode {
    spec fn is_leaf(&self) -> bool {
        match self {
            TreeNode::Nil => false,
            TreeNode::Cons(_, left, right) => **left == TreeNode::Nil && **right == TreeNode::Nil
        }
    }
}

fn hasPathSum(root: TreeNode, targetSum: int) -> (b: bool)
    ensures
        b ==> exists|p: Seq<TreeNode>| isPath(p, root) && pathSum(p) == targetSum
{
    match root {
        TreeNode::Nil => false,
        TreeNode::Cons(val, left, right) => {
            if **left == TreeNode::Nil && **right == TreeNode::Nil {
                // Leaf node
                if val == targetSum {
                    assert(isPath(seq![root], root));
                    assert(pathSum(seq![root]) == val);
                    true
                } else {
                    false
                }
            } else {
                let left_result = if **left != TreeNode::Nil {
                    hasPathSum(**left, targetSum - val)
                } else {
                    false
                };
                
                let right_result = if **right != TreeNode::Nil {
                    hasPathSum(**right, targetSum - val)
                } else {
                    false
                };
                
                if left_result {
                    // There exists a path in left subtree
                    assert(exists|p: Seq<TreeNode>| isPath(p, **left) && pathSum(p) == targetSum - val);
                    true
                } else if right_result {
                    // There exists a path in right subtree  
                    assert(exists|p: Seq<TreeNode>| isPath(p, **right) && pathSum(p) == targetSum - val);
                    true
                } else {
                    false
                }
            }
        }
    }
}

}