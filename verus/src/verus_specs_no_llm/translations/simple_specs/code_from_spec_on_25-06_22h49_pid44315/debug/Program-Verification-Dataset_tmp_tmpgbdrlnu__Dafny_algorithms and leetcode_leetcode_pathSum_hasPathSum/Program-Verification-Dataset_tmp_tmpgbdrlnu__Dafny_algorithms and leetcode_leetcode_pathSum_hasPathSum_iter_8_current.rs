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
        TreeNode::Cons(_, left, right) => 1 + max_nat(tree_height(*left), tree_height(*right))
    }
}

spec fn isPath(paths: Seq<TreeNode>, root: TreeNode) -> bool 
    decreases paths.len()
{
    if paths.len() == 0 {
        false 
    } else {
        match paths[0] {
            TreeNode::Nil => false,
            TreeNode::Cons(val, left, right) => 
                if paths.len() == 1 {
                    root == paths[0] && root.is_leaf()
                } else {
                    root == paths[0] && 
                    (isPath(paths.subrange(1, paths.len() as int), *left) || 
                     isPath(paths.subrange(1, paths.len() as int), *right))
                }
        }
    }
}

spec fn pathSum(paths: Seq<TreeNode>) -> int 
    decreases paths.len()
{
    if paths.len() == 0 {
        0 
    } else {
        match paths[0] {
            TreeNode::Nil => 0,
            TreeNode::Cons(val, _, _) => val + pathSum(paths.subrange(1, paths.len() as int))
        }
    }
}

impl TreeNode {
    spec fn is_leaf(&self) -> bool {
        match self {
            TreeNode::Nil => false,
            TreeNode::Cons(_, left, right) => *left == TreeNode::Nil && *right == TreeNode::Nil
        }
    }
}

proof fn lemma_subrange_properties(s: Seq<TreeNode>)
    requires s.len() > 0
    ensures 
        s.subrange(1, s.len() as int).len() == s.len() - 1,
        forall|i: int| 0 <= i < s.subrange(1, s.len() as int).len() ==> 
            s.subrange(1, s.len() as int)[i] == s[i + 1]
{
}

proof fn lemma_seq_add_properties(s1: Seq<TreeNode>, s2: Seq<TreeNode>)
    ensures
        s1.add(s2).len() == s1.len() + s2.len(),
        s1.add(s2).subrange(s1.len() as int, (s1.len() + s2.len()) as int) =~= s2,
        forall|i: int| 0 <= i < s1.len() ==> s1.add(s2)[i] == s1[i],
        forall|i: int| 0 <= i < s2.len() ==> s1.add(s2)[s1.len() + i] == s2[i]
{
}

proof fn lemma_path_construction(root: TreeNode, subtree_path: Seq<TreeNode>, subtree: TreeNode, target_sum: int)
    requires
        root matches TreeNode::Cons(val, left, right),
        subtree == *left || subtree == *right,
        isPath(subtree_path, subtree),
        pathSum(subtree_path) == target_sum - val,
        subtree_path.len() > 0,
    ensures
        exists|full_path: Seq<TreeNode>| isPath(full_path, root) && pathSum(full_path) == target_sum
{
    let TreeNode::Cons(val, left, right) = root;
    let full_path = seq![root].add(subtree_path);
    
    proof {
        lemma_seq_add_properties(seq![root], subtree_path);
        lemma_subrange_properties(full_path);
        
        assert(full_path.len() == 1 + subtree_path.len());
        assert(full_path[0] == root);
        assert(full_path.subrange(1, full_path.len() as int) =~= subtree_path);
        
        // Prove isPath property
        if subtree == *left {
            assert(isPath(subtree_path, *left));
            assert(isPath(full_path.subrange(1, full_path.len() as int), *left));
            assert(isPath(full_path, root));
        } else {
            assert(subtree == *right);
            assert(isPath(subtree_path, *right));
            assert(isPath(full_path.subrange(1, full_path.len() as int), *right));
            assert(isPath(full_path, root));
        }
        
        // Prove pathSum property
        assert(pathSum(full_path) == val + pathSum(full_path.subrange(1, full_path.len() as int)));
        assert(pathSum(full_path.subrange(1, full_path.len() as int)) == pathSum(subtree_path));
        assert(pathSum(subtree_path) == target_sum - val);
        assert(pathSum(full_path) == val + (target_sum - val));
        assert(pathSum(full_path) == target_sum);
    }
}

fn hasPathSum(root: TreeNode, targetSum: int) -> (b: bool)
    ensures
        b ==> exists|p: Seq<TreeNode>| isPath(p, root) && pathSum(p) == targetSum
    decreases tree_height(root)
{
    match root {
        TreeNode::Nil => false,
        TreeNode::Cons(val, left, right) => {
            if *left == TreeNode::Nil && *right == TreeNode::Nil {
                // Leaf node
                if val == targetSum {
                    proof {
                        assert(root.is_leaf());
                        let ghost witness_path = seq![root];
                        assert(witness_path.len() == 1);
                        assert(witness_path[0] == root);
                        assert(isPath(witness_path, root)) by {
                            assert(witness_path.len() == 1);
                            assert(witness_path[0] == root);
                            assert(root.is_leaf());
                        }
                        assert(pathSum(witness_path) == val) by {
                            assert(pathSum(witness_path) == val + pathSum(witness_path.subrange(1, 1)));
                            assert(witness_path.subrange(1, 1).len() == 0);
                            assert(pathSum(witness_path.subrange(1, 1)) == 0);
                        }
                        assert(pathSum(witness_path) == targetSum);
                    }
                    true
                } else {
                    false
                }
            } else {
                // Internal node - check both subtrees
                let mut found = false;
                
                // Check left subtree if it's not Nil
                if *left != TreeNode::Nil {
                    let left_result = hasPathSum(*left, targetSum - val);
                    if left_result {
                        proof {
                            // Get the witness path from the left subtree
                            assert(exists|p: Seq<TreeNode>| isPath(p, *left) && pathSum(p) == targetSum - val);
                            let ghost subtree_path = choose|p: Seq<TreeNode>| isPath(p, *left) && pathSum(p) == targetSum - val;
                            assert(subtree_path.len() > 0) by {
                                assert(isPath(subtree_path, *left));
                                assert(subtree_path.len() > 0);
                            }
                            lemma_path_construction(root, subtree_path, *left, targetSum);
                        }
                        found = true;
                    }
                }
                
                // Check right subtree if we haven't found a path and it's not Nil
                if !found && *right != TreeNode::Nil {
                    let right_result = hasPathSum(*right, targetSum - val);
                    if right_result {
                        proof {
                            // Get the witness path from the right subtree
                            assert(exists|p: Seq<TreeNode>| isPath(p, *right) && pathSum(p) == targetSum - val);
                            let ghost subtree_path = choose|p: Seq<TreeNode>| isPath(p, *right) && pathSum(p) == targetSum - val;
                            assert(subtree_path.len() > 0) by {
                                assert(isPath(subtree_path, *right));
                                assert(subtree_path.len() > 0);
                            }
                            lemma_path_construction(root, subtree_path, *right, targetSum);
                        }
                        found = true;
                    }
                }
                
                found
            }
        }
    }
}

}