use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum TreeNode {
    Nil,
    Cons { val: nat, left: Box<TreeNode>, right: Box<TreeNode> }
}

pub spec fn TreeSeq(root: TreeNode) -> Seq<TreeNode>
    decreases root
{
    match root {
        TreeNode::Nil => seq![TreeNode::Nil],
        TreeNode::Cons { val, left, right } => seq![root] + TreeSeq(*left) + TreeSeq(*right)
    }
}

pub spec fn TreeSet(root: TreeNode) -> Set<TreeNode>
    decreases root
{
    match root {
        TreeNode::Nil => set![TreeNode::Nil],
        TreeNode::Cons { val, left, right } => TreeSet(*left) + set![root] + TreeSet(*right)
    }
}

pub spec fn isPath(paths: Seq<TreeNode>, root: TreeNode) -> bool
    decreases paths.len()
{
    if paths.len() == 0 {
        false
    } else {
        match paths[0] {
            TreeNode::Nil => false,
            TreeNode::Cons { val, left, right } => {
                if paths.len() == 1 {
                    root == paths[0]
                } else {
                    root == paths[0] && (isPath(paths.subrange(1, paths.len() as int), *left) || isPath(paths.subrange(1, paths.len() as int), *right))
                }
            }
        }
    }
}

pub spec fn pathSum(paths: Seq<TreeNode>) -> nat
    decreases paths.len()
{
    if paths.len() == 0 {
        0
    } else {
        match paths[0] {
            TreeNode::Nil => 0,
            TreeNode::Cons { val, left, right } => val + pathSum(paths.subrange(1, paths.len() as int))
        }
    }
}

pub fn hasPathSum(root: TreeNode, targetSum: int) -> (b: bool)
    ensures(b ==> exists|p: Seq<TreeNode>| isPath(p, root) && pathSum(p) == targetSum)
{
}

pub fn Test()
{
}

}