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

spec fn max_nat(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

spec fn tree_height(tree: TreeNode) -> nat
    decreases tree
{
    match tree {
        TreeNode::Nil => 0,
        TreeNode::Cons(_, left, right) => 1 + max_nat(tree_height(**left), tree_height(**right))
    }
}

spec fn isPath(paths: Seq<TreeNode>, root: TreeNode) -> bool 
    decreases paths.len()
{
    if paths.len() == 0 then 
        false 
    else match paths.spec_index(0) {
        TreeNode::Nil => false,
        TreeNode::Cons(val, left, right) => 
            if paths.len() == 1 then 
                root == paths.spec_index(0) && root.is_leaf()
            else 
                root == paths.spec_index(0) && 
                (isPath(paths.subrange(1, paths.len() as int), **left) || 
                 isPath(paths.subrange(1, paths.len() as int), **right))
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

proof fn lemma_path_construction(root: TreeNode, subtree_path: Seq<TreeNode>, subtree: TreeNode, target_sum: int)
    requires
        root matches TreeNode::Cons(val, left, right),
        subtree == **left || subtree == **right,
        isPath(subtree_path, subtree),
        pathSum(subtree_path) == target_sum - val
    ensures
        exists|full_path: Seq<TreeNode>| isPath(full_path, root) && pathSum(full_path) == target_sum
{
    let TreeNode::Cons(val, left, right) = root;
    let full_path = seq![root].add(subtree_path);
    
    assert(full_path.len() > 1);
    assert(full_path.spec_index(0) == root);
    assert(full_path.subrange(1, full_path.len() as int) == subtree_path);
    
    // Prove isPath property
    if subtree == **left {
        assert(isPath(subtree_path, **left));
        assert(isPath(full_path.subrange(1, full_path.len() as int), **left));
        assert(isPath(full_path, root));
    } else {
        assert(subtree == **right);
        assert(isPath(subtree_path, **right));
        assert(isPath(full_path.subrange(1, full_path.len() as int), **right));
        assert(isPath(full_path, root));
    }
    
    // Prove pathSum property
    assert(pathSum(full_path) == val + pathSum(full_path.subrange(1, full_path.len() as int)));
    assert(pathSum(full_path.subrange(1, full_path.len() as int)) == pathSum(subtree_path));
    assert(pathSum(full_path) == val + pathSum(subtree_path));
    assert(pathSum(full_path) == val + (target_sum - val));
    assert(pathSum(full_path) == target_sum);
    
    // The witness exists
    assert(isPath(full_path, root) && pathSum(full_path) == target_sum);
}

fn hasPathSum(root: TreeNode, targetSum: int) -> (b: bool)
    ensures
        b ==> exists|p: Seq<TreeNode>| isPath(p, root) && pathSum(p) == targetSum
    decreases tree_height(root)
{
    match root {
        TreeNode::Nil => false,
        TreeNode::Cons(val, left, right) => {
            if **left == TreeNode::Nil && **right == TreeNode::Nil {
                // Leaf node
                if val == targetSum {
                    assert(root.is_leaf());
                    let ghost witness_path = seq![root];
                    assert(witness_path.len() == 1);
                    assert(witness_path.spec_index(0) == root);
                    assert(isPath(witness_path, root));
                    assert(pathSum(witness_path) == val);
                    assert(pathSum(witness_path) == targetSum);
                    true
                } else {
                    false
                }
            } else {
                // Prove termination measures
                assert(tree_height(**left) < tree_height(root)) by {
                    let left_height = tree_height(**left);
                    let right_height = tree_height(**right);
                    let max_height = max_nat(left_height, right_height);
                    assert(tree_height(root) == 1 + max_height);
                    assert(max_height >= left_height);
                    assert(1 + max_height > max_height);
                    assert(max_height >= left_height);
                };
                
                assert(tree_height(**right) < tree_height(root)) by {
                    let left_height = tree_height(**left);
                    let right_height = tree_height(**right);
                    let max_height = max_nat(left_height, right_height);
                    assert(tree_height(root) == 1 + max_height);
                    assert(max_height >= right_height);
                    assert(1 + max_height > max_height);
                    assert(max_height >= right_height);
                };
                
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
                    assert(exists|p: Seq<TreeNode>| isPath(p, **left) && pathSum(p) == targetSum - val);
                    let ghost subtree_path = choose|p: Seq<TreeNode>| isPath(p, **left) && pathSum(p) == targetSum - val;
                    proof {
                        lemma_path_construction(root, subtree_path, **left, targetSum);
                    }
                    true
                } else if right_result {
                    assert(exists|p: Seq<TreeNode>| isPath(p, **right) && pathSum(p) == targetSum - val);
                    let ghost subtree_path = choose|p: Seq<TreeNode>| isPath(p, **right) && pathSum(p) == targetSum - val;
                    proof {
                        lemma_path_construction(root, subtree_path, **right, targetSum);
                    }
                    true
                } else {
                    false
                }
            }
        }
    }
}

}