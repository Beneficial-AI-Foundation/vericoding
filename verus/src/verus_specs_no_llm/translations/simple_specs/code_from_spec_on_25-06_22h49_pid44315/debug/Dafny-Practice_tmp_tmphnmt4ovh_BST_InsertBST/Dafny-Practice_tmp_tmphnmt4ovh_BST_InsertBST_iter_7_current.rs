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

// Helper spec function to check if all elements in a tree satisfy bounds
spec fn all_elements_bounded(t: Tree, lower: Option<int>, upper: Option<int>) -> bool {
    forall|x: int| NumbersInTree(t).contains(x) ==> {
        (lower.is_none() || lower.unwrap() < x) &&
        (upper.is_none() || x < upper.unwrap())
    }
}

// Lemma: elements in inorder traversal respect bounds
proof fn lemma_inorder_bounds(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures forall|i: int| 0 <= i < Inorder(t).len() ==> {
        let val = Inorder(t)[i];
        (lower.is_none() || lower.unwrap() < val) &&
        (upper.is_none() || val < upper.unwrap())
    }
    decreases t
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
            
            // Properties about the combined sequence
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![data] + right_seq;
            
            assert(left_seq + seq![data] + right_seq == full_seq);
            assert(full_seq.len() == left_seq.len() + 1 + right_seq.len());
            
            // Properties for left part
            assert forall|i: int| 0 <= i < left_seq.len() ==> {
                full_seq[i] == left_seq[i] &&
                (lower.is_none() || lower.unwrap() < full_seq[i]) &&
                full_seq[i] < data
            } by {
                if 0 <= i < left_seq.len() {
                    assert(full_seq[i] == left_seq[i]);
                }
            };
            
            // Property for middle element
            if left_seq.len() < full_seq.len() {
                assert(full_seq[left_seq.len()] == data);
            }
            
            // Properties for right part
            assert forall|i: int| 0 <= i < right_seq.len() ==> {
                let full_idx = left_seq.len() + 1 + i;
                full_idx < full_seq.len() &&
                full_seq[full_idx] == right_seq[i] &&
                data < full_seq[full_idx] &&
                (upper.is_none() || full_seq[full_idx] < upper.unwrap())
            } by {
                if 0 <= i < right_seq.len() {
                    let full_idx = left_seq.len() + 1 + i;
                    assert(full_idx < full_seq.len());
                    assert(full_seq[full_idx] == right_seq[i]);
                }
            };
        }
    }
}

// Lemma: bounded BST has ascending inorder traversal
proof fn lemma_bounded_inorder_ascending(t: Tree, lower: Option<int>, upper: Option<int>)
    requires BST_bounded(t, lower, upper)
    ensures Ascending(Inorder(t))
    decreases t
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            lemma_bounded_inorder_ascending(*left, lower, Some(data));
            lemma_bounded_inorder_ascending(*right, Some(data), upper);
            lemma_inorder_bounds(*left, lower, Some(data));
            lemma_inorder_bounds(*right, Some(data), upper);
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![data] + right_seq;
            
            assert forall|i: int, j: int| 0 <= i < j < full_seq.len() ==> 
                full_seq[i] < full_seq[j] by {
                if 0 <= i < j < full_seq.len() {
                    if j < left_seq.len() {
                        // Both in left subtree - use left BST property
                        assert(Ascending(left_seq));
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
                        assert(left_seq[i] < data);
                        assert(data < right_seq[right_idx]);
                    } else if i == left_seq.len() && j > left_seq.len() {
                        // i is data, j in right
                        let right_idx = j - left_seq.len() - 1;
                        assert(0 <= right_idx < right_seq.len());
                        assert(full_seq[i] == data);
                        assert(full_seq[j] == right_seq[right_idx]);
                        assert(data < right_seq[right_idx]);
                    } else if i > left_seq.len() && j > left_seq.len() {
                        // Both in right subtree - use right BST property
                        let right_i = i - left_seq.len() - 1;
                        let right_j = j - left_seq.len() - 1;
                        assert(0 <= right_i < right_j < right_seq.len());
                        assert(Ascending(right_seq));
                        assert(right_seq[right_i] < right_seq[right_j]);
                    }
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

// Helper lemma: if BST and all elements in subtree are bounded, then subtree is BST_bounded
proof fn lemma_BST_bounded_from_bounds(t: Tree, lower: Option<int>, upper: Option<int>)
    requires 
        BST(t),
        all_elements_bounded(t, lower, upper)
    ensures BST_bounded(t, lower, upper)
    decreases t
{
    match t {
        Tree::Leaf => {},
        Tree::Node { left, data, right } => {
            // Show that data satisfies bounds
            assert(NumbersInTree(t).contains(data));
            assert(lower.is_none() || lower.unwrap() < data);
            assert(upper.is_none() || data < upper.unwrap());
            
            // Show that left subtree elements are bounded by (lower, Some(data))
            assert(all_elements_bounded(*left, lower, Some(data))) by {
                assert forall|x: int| NumbersInTree(*left).contains(x) ==> {
                    (lower.is_none() || lower.unwrap() < x) && x < data
                } by {
                    if NumbersInTree(*left).contains(x) {
                        assert(NumbersInTree(t).contains(x));
                        assert(all_elements_bounded(t, lower, upper));
                        assert(lower.is_none() || lower.unwrap() < x);
                        
                        // Show x < data using BST property
                        let inorder_seq = Inorder(t);
                        let left_seq = Inorder(*left);
                        assert(inorder_seq == left_seq + seq![data] + Inorder(*right));
                        assert(Ascending(inorder_seq));
                        
                        // x appears in left_seq, so x appears before data in inorder_seq
                        assert exists|i: int| 0 <= i < left_seq.len() && left_seq[i] == x;
                        let i = choose|i: int| 0 <= i < left_seq.len() && left_seq[i] == x;
                        assert(inorder_seq[i] == x);
                        assert(inorder_seq[left_seq.len()] == data);
                        assert(i < left_seq.len());
                        assert(inorder_seq[i] < inorder_seq[left_seq.len()]);
                        assert(x < data);
                    }
                };
            };
            
            // Show that right subtree elements are bounded by (Some(data), upper)
            assert(all_elements_bounded(*right, Some(data), upper)) by {
                assert forall|x: int| NumbersInTree(*right).contains(x) ==> {
                    data < x && (upper.is_none() || x < upper.unwrap())
                } by {
                    if NumbersInTree(*right).contains(x) {
                        assert(NumbersInTree(t).contains(x));
                        assert(all_elements_bounded(t, lower, upper));
                        assert(upper.is_none() || x < upper.unwrap());
                        
                        // Show data < x using BST property
                        let inorder_seq = Inorder(t);
                        let left_seq = Inorder(*left);
                        let right_seq = Inorder(*right);
                        assert(inorder_seq == left_seq + seq![data] + right_seq);
                        assert(Ascending(inorder_seq));
                        
                        // x appears in right_seq, so x appears after data in inorder_seq
                        assert exists|i: int| 0 <= i < right_seq.len() && right_seq[i] == x;
                        let i = choose|i: int| 0 <= i < right_seq.len() && right_seq[i] == x;
                        let full_idx = left_seq.len() + 1 + i;
                        assert(inorder_seq[full_idx] == x);
                        assert(inorder_seq[left_seq.len()] == data);
                        assert(left_seq.len() < full_idx);
                        assert(inorder_seq[left_seq.len()] < inorder_seq[full_idx]);
                        assert(data < x);
                    }
                };
            };
            
            // Recursively prove for subtrees
            lemma_BST_bounded_from_bounds(*left, lower, Some(data));
            lemma_BST_bounded_from_bounds(*right, Some(data), upper);
        }
    }
}

// Helper lemma to establish bounds for BST with no external bounds
proof fn lemma_BST_to_bounded_unbounded(t: Tree)
    requires BST(t)
    ensures BST_bounded(t, None, None)
{
    assert(all_elements_bounded(t, None, None)) by {
        assert forall|x: int| NumbersInTree(t).contains(x) ==> {
            (None.is_none() || None.unwrap() < x) &&
            (None.is_none() || x < None.unwrap())
        } by {
            // This is trivially true since None.is_none() is always true
        };
    };
    
    lemma_BST_bounded_from_bounds(t, None, None);
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
                assert(x > data); // Since x != data and x < data is false
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