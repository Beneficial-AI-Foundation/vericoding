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
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q.spec_index(i) < q.spec_index(j)
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

// Lemma: elements in inorder traversal respect bounds
proof fn lemma_inorder_bounds(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures forall|i: int| 0 <= i < Inorder(t).len() ==> {
        let val = Inorder(t).spec_index(i);
        (lower.is_none() || lower.unwrap() < val) &&
        (upper.is_none() || val < upper.unwrap())
    }
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
            
            // Assert properties about the combined sequence
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![data] + right_seq;
            
            assert forall|i: int| 0 <= i < left_seq.len() ==> {
                full_seq.spec_index(i) == left_seq.spec_index(i)
            } by {
                // Verus can prove this automatically for sequence concatenation
            };
            
            assert forall|i: int| 0 <= i < right_seq.len() ==> {
                full_seq.spec_index(left_seq.len() + 1 + i) == right_seq.spec_index(i)
            } by {
                // Verus can prove this automatically for sequence concatenation
            };

            assert(full_seq.spec_index(left_seq.len()) == data);
        }
    }
}

// Lemma: bounded BST has ascending inorder traversal
proof fn lemma_bounded_inorder_ascending(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures Ascending(Inorder(t))
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_bounded_inorder_ascending(*left, lower, Some(data));
            lemma_bounded_inorder_ascending(*right, Some(data), upper);
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
            
            // Prove that the combined sequence is ascending
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![data] + right_seq;
            
            assert forall|i: int, j: int| 0 <= i < j < full_seq.len() ==> 
                full_seq.spec_index(i) < full_seq.spec_index(j) by {
                if j < left_seq.len() {
                    // Both in left subtree
                    assert(full_seq.spec_index(i) == left_seq.spec_index(i));
                    assert(full_seq.spec_index(j) == left_seq.spec_index(j));
                } else if i < left_seq.len() && j == left_seq.len() {
                    // i in left, j is data
                    assert(full_seq.spec_index(i) == left_seq.spec_index(i));
                    assert(full_seq.spec_index(j) == data);
                } else if i < left_seq.len() && j > left_seq.len() {
                    // i in left, j in right
                    assert(full_seq.spec_index(i) == left_seq.spec_index(i));
                    assert(full_seq.spec_index(j) == right_seq.spec_index(j - left_seq.len() - 1));
                } else if i == left_seq.len() && j > left_seq.len() {
                    // i is data, j in right
                    assert(full_seq.spec_index(i) == data);
                    assert(full_seq.spec_index(j) == right_seq.spec_index(j - left_seq.len() - 1));
                } else if i > left_seq.len() && j > left_seq.len() {
                    // Both in right subtree
                    assert(full_seq.spec_index(i) == right_seq.spec_index(i - left_seq.len() - 1));
                    assert(full_seq.spec_index(j) == right_seq.spec_index(j - left_seq.len() - 1));
                }
            };
        }
    }
}

// Lemma: BST_bounded implies BST
proof fn lemma_BST_bounded_implies_BST(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures BST(t)
{
    lemma_bounded_inorder_ascending(t, lower, upper);
}

// Lemma: BST implies BST_bounded with any compatible bounds
proof fn lemma_BST_implies_BST_bounded(t: Tree, lower: Option<int>, upper: Option<int>)
    requires 
        BST(t),
        forall|i: int| 0 <= i < Inorder(t).len() ==> {
            let val = Inorder(t).spec_index(i);
            (lower.is_none() || lower.unwrap() < val) &&
            (upper.is_none() || val < upper.unwrap())
        }
    ensures BST_bounded(t, lower, upper)
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            // Establish bounds for subtrees
            assert forall|i: int| 0 <= i < Inorder(*left).len() ==> {
                let val = Inorder(*left).spec_index(i);
                (lower.is_none() || lower.unwrap() < val) &&
                val < data
            } by {
                let full_seq = Inorder(t);
                let left_seq = Inorder(*left);
                assert forall|i: int| 0 <= i < left_seq.len() ==> 
                    full_seq.spec_index(i) == left_seq.spec_index(i) by {};
            };
            
            assert forall|i: int| 0 <= i < Inorder(*right).len() ==> {
                let val = Inorder(*right).spec_index(i);
                data < val &&
                (upper.is_none() || val < upper.unwrap())
            } by {
                let full_seq = Inorder(t);
                let left_seq = Inorder(*left);
                let right_seq = Inorder(*right);
                assert forall|i: int| 0 <= i < right_seq.len() ==> 
                    full_seq.spec_index(left_seq.len() + 1 + i) == right_seq.spec_index(i) by {};
            };
            
            lemma_BST_implies_BST_bounded(*left, lower, Some(data));
            lemma_BST_implies_BST_bounded(*right, Some(data), upper);
        }
    }
}

// Helper lemma to establish bounds for BST with no external bounds
proof fn lemma_BST_to_bounded_unbounded(t: Tree)
    requires BST(t)
    ensures BST_bounded(t, None, None)
{
    assert forall|i: int| 0 <= i < Inorder(t).len() ==> {
        let val = Inorder(t).spec_index(i);
        true // No bounds to check
    } by {};
    lemma_BST_implies_BST_bounded(t, None, None);
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