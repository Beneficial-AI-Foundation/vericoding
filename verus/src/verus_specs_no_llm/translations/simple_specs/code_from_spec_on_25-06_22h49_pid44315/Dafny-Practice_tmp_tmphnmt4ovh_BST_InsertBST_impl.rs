use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define the Tree data structure
pub enum Tree {
    Leaf,
    Node { left: Box<Tree>, data: int, right: Box<Tree> }
}

// Inorder traversal of the tree
spec fn Inorder(t: Tree) -> Seq<int> {
    match t {
        Tree::Leaf => seq![],
        Tree::Node { left, data, right } => Inorder(*left) + seq![data] + Inorder(*right)
    }
}

// Numbers contained in the tree
spec fn NumbersInTree(t: Tree) -> Set<int> {
    match t {
        Tree::Leaf => set![],
        Tree::Node { left, data, right } => NumbersInTree(*left).union(set![data]).union(NumbersInTree(*right))
    }
}

spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

// Helper function to check if a tree satisfies BST property with bounds
spec fn BST_bounded(t: Tree, lower: Option<int>, upper: Option<int>) -> bool {
    match t {
        Tree::Leaf => true,
        Tree::Node { left, data, right } => {
            (lower.is_none() || lower.unwrap() < data) &&
            (upper.is_none() || data < upper.unwrap()) &&
            BST_bounded(*left, lower, Some(data)) &&
            BST_bounded(*right, Some(data), upper)
        }
    }
}

proof fn lemma_BST_bounded_implies_BST(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures BST(t)
    decreases t
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_BST_bounded_implies_BST(*left, lower, Some(data));
            lemma_BST_bounded_implies_BST(*right, Some(data), upper);
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![data] + right_seq;
            
            assert(full_seq == Inorder(t));
            
            assert forall|i: int, j: int| 0 <= i < j < full_seq.len() ==> 
                full_seq[i] < full_seq[j] by {
                if 0 <= i < j < full_seq.len() {
                    if j < left_seq.len() {
                        // Both in left subtree
                        assert(full_seq[i] == left_seq[i]);
                        assert(full_seq[j] == left_seq[j]);
                    } else if i < left_seq.len() && j == left_seq.len() {
                        // i in left, j is data
                        assert(full_seq[i] == left_seq[i]);
                        assert(full_seq[j] == data);
                        assert(left_seq[i] < data);
                    } else if i < left_seq.len() && j > left_seq.len() {
                        // i in left, j in right
                        let right_idx = j - left_seq.len() - 1;
                        assert(0 <= right_idx < right_seq.len());
                        assert(full_seq[i] == left_seq[i]);
                        assert(full_seq[j] == right_seq[right_idx]);
                        assert(left_seq[i] < data && data < right_seq[right_idx]);
                    } else if i == left_seq.len() && j > left_seq.len() {
                        // i is data, j in right
                        let right_idx = j - left_seq.len() - 1;
                        assert(0 <= right_idx < right_seq.len());
                        assert(full_seq[i] == data);
                        assert(full_seq[j] == right_seq[right_idx]);
                        assert(data < right_seq[right_idx]);
                    } else {
                        // Both in right subtree
                        let right_i = i - left_seq.len() - 1;
                        let right_j = j - left_seq.len() - 1;
                        assert(0 <= right_i < right_j < right_seq.len());
                        assert(right_seq[right_i] < right_seq[right_j]);
                        assert(full_seq[i] == right_seq[right_i]);
                        assert(full_seq[j] == right_seq[right_j]);
                    }
                }
            };
        }
    }
}

proof fn lemma_BST_to_bounded_unbounded(t: Tree)
    requires BST(t)
    ensures BST_bounded(t, None, None)
    decreases t
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = Inorder(t);
            
            assert(full_seq == left_seq + seq![data] + right_seq);
            
            // Prove left subtree is BST
            assert(Ascending(left_seq)) by {
                assert forall|i: int, j: int| 0 <= i < j < left_seq.len() ==> 
                    left_seq[i] < left_seq[j] by {
                    if 0 <= i < j < left_seq.len() {
                        assert(full_seq[i] == left_seq[i]);
                        assert(full_seq[j] == left_seq[j]);
                    }
                };
            };
            
            // Prove right subtree is BST
            assert(Ascending(right_seq)) by {
                assert forall|i: int, j: int| 0 <= i < j < right_seq.len() ==> 
                    right_seq[i] < right_seq[j] by {
                    if 0 <= i < j < right_seq.len() {
                        let full_i = left_seq.len() + 1 + i;
                        let full_j = left_seq.len() + 1 + j;
                        assert(full_seq[full_i] == right_seq[i]);
                        assert(full_seq[full_j] == right_seq[j]);
                    }
                };
            };
            
            lemma_BST_to_bounded_unbounded(*left);
            lemma_BST_to_bounded_unbounded(*right);
        }
    }
}

// Helper function for insertion with bounds
fn InsertBST_helper(t0: Tree, x: int, lower: Option<int>, upper: Option<int>) -> (t: Tree)
    requires
        BST_bounded(t0, lower, upper),
        (lower.is_none() || lower.unwrap() < x),
        (upper.is_none() || x < upper.unwrap()),
        !NumbersInTree(t0).contains(x)
    ensures
        BST_bounded(t, lower, upper),
        NumbersInTree(t) == NumbersInTree(t0).insert(x)
    decreases t0
{
    match t0 {
        Tree::Leaf => {
            Tree::Node { 
                left: Box::new(Tree::Leaf), 
                data: x, 
                right: Box::new(Tree::Leaf) 
            }
        },
        Tree::Node { left, data, right } => {
            if x < data {
                let new_left = InsertBST_helper(*left, x, lower, Some(data));
                Tree::Node { 
                    left: Box::new(new_left), 
                    data: data, 
                    right: right 
                }
            } else {
                // Since x != data (from precondition) and x < data is false, we have x > data
                let new_right = InsertBST_helper(*right, x, Some(data), upper);
                Tree::Node { 
                    left: left, 
                    data: data, 
                    right: Box::new(new_right) 
                }
            }
        }
    }
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires
        BST(t0) && !(NumbersInTree(t0).contains(x))
    ensures
        BST(t) && NumbersInTree(t) == NumbersInTree(t0).insert(x)
{
    proof {
        lemma_BST_to_bounded_unbounded(t0);
    }
    let result = InsertBST_helper(t0, x, None, None);
    proof {
        lemma_BST_bounded_implies_BST(result, None, None);
    }
    result
}

}