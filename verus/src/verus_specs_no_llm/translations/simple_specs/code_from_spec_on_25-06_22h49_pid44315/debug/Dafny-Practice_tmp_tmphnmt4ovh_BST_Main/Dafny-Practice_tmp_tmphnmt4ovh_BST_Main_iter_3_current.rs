use builtin::*;
use builtin_macros::*;

verus! {

// Tree datatype definition
pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

fn main() {
}

// Specification functions
spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

spec fn Ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn NoDuplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

spec fn Inorder(t: Tree) -> Seq<int>
    decreases t
{
    match t {
        Tree::Empty => seq![],
        Tree::Node(n, left, right) => Inorder(*left) + seq![n] + Inorder(*right)
    }
}

spec fn NumbersInTree(t: Tree) -> Set<int>
    decreases t
{
    match t {
        Tree::Empty => set![],
        Tree::Node(n, left, right) => NumbersInTree(*left).union(set![n]).union(NumbersInTree(*right))
    }
}

spec fn NumbersInSequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| exists|i: int| 0 <= i < q.len() && q[i] == x)
}

// Additional helper spec functions
spec fn BST_property(t: Tree) -> bool
    decreases t
{
    match t {
        Tree::Empty => true,
        Tree::Node(n, left, right) => {
            BST_property(*left) && BST_property(*right) &&
            (forall|x: int| NumbersInTree(*left).contains(x) ==> x < n) &&
            (forall|x: int| NumbersInTree(*right).contains(x) ==> n < x)
        }
    }
}

// Lemma to establish equivalence between BST and BST_property
proof fn lemma_BST_equiv(t: Tree)
    ensures BST(t) <==> BST_property(t)
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_BST_equiv(*left);
            lemma_BST_equiv(*right);
            if BST_property(t) {
                lemma_inorder_reflects_tree_structure(t);
            }
            if BST(t) {
                lemma_ascending_implies_bst_property(t);
            }
        }
    }
}

// Lemma about inorder traversal structure
proof fn lemma_inorder_reflects_tree_structure(t: Tree)
    requires BST_property(t)
    ensures BST(t)
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_inorder_reflects_tree_structure(*left);
            lemma_inorder_reflects_tree_structure(*right);
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![n] + right_seq;
            
            assert forall|i: int, j: int| 0 <= i < j < full_seq.len() implies full_seq[i] < full_seq[j] by {
                if j < left_seq.len() {
                    // Both in left part - follows from BST(*left)
                } else if i < left_seq.len() && j == left_seq.len() {
                    // i in left, j is n
                    lemma_inorder_contains_tree_numbers(*left);
                    assert(NumbersInTree(*left).contains(left_seq[i]));
                } else if i < left_seq.len() && j > left_seq.len() {
                    // i in left, j in right
                    lemma_inorder_contains_tree_numbers(*left);
                    lemma_inorder_contains_tree_numbers(*right);
                    assert(NumbersInTree(*left).contains(left_seq[i]));
                    assert(NumbersInTree(*right).contains(right_seq[j - left_seq.len() - 1]));
                } else if i == left_seq.len() && j > left_seq.len() {
                    // i is n, j in right
                    lemma_inorder_contains_tree_numbers(*right);
                    assert(NumbersInTree(*right).contains(right_seq[j - left_seq.len() - 1]));
                } else {
                    // Both in right part - follows from BST(*right)
                }
            }
        }
    }
}

proof fn lemma_ascending_implies_bst_property(t: Tree)
    requires BST(t)
    ensures BST_property(t)
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_ascending_implies_bst_property(*left);
            lemma_ascending_implies_bst_property(*right);
            
            // Additional reasoning to establish the ordering properties
            lemma_inorder_contains_tree_numbers(*left);
            lemma_inorder_contains_tree_numbers(*right);
        }
    }
}

proof fn lemma_inorder_contains_tree_numbers(t: Tree)
    ensures forall|x: int| NumbersInTree(t).contains(x) ==> 
            exists|i: int| 0 <= i < Inorder(t).len() && Inorder(t)[i] == x
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_inorder_contains_tree_numbers(*left);
            lemma_inorder_contains_tree_numbers(*right);
        }
    }
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires 
        BST(t0),
        !(NumbersInTree(t0).contains(x))
    ensures 
        BST(t),
        NumbersInTree(t) == NumbersInTree(t0).insert(x)
    decreases t0
{
    proof {
        lemma_BST_equiv(t0);
    }
    
    match t0 {
        Tree::Empty => {
            let result = Tree::Node(x, box Tree::Empty, box Tree::Empty);
            proof {
                assert(BST_property(result));
                lemma_BST_equiv(result);
            }
            result
        },
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = InsertBST(*left, x);
                let result = Tree::Node(n, box new_left, box *right);
                proof {
                    lemma_BST_equiv(*left);
                    lemma_BST_equiv(*right);
                    lemma_BST_equiv(new_left);
                    
                    // Prove BST_property for result
                    assert(BST_property(*right));
                    assert(NumbersInTree(new_left) == NumbersInTree(*left).insert(x));
                    
                    // Prove ordering properties
                    assert forall|y: int| NumbersInTree(new_left).contains(y) implies y < n by {
                        if NumbersInTree(*left).contains(y) {
                            assert(y < n);
                        } else {
                            assert(y == x);
                            assert(x < n);
                        }
                    }
                    assert(forall|y: int| NumbersInTree(*right).contains(y) ==> n < y);
                    assert(BST_property(result));
                    lemma_BST_equiv(result);
                }
                result
            } else {
                let new_right = InsertBST(*right, x);
                let result = Tree::Node(n, box *left, box new_right);
                proof {
                    lemma_BST_equiv(*left);
                    lemma_BST_equiv(*right);
                    lemma_BST_equiv(new_right);
                    
                    // Prove BST_property for result
                    assert(BST_property(*left));
                    assert(NumbersInTree(new_right) == NumbersInTree(*right).insert(x));
                    assert(forall|y: int| NumbersInTree(*left).contains(y) ==> y < n);
                    
                    // Prove ordering properties
                    assert forall|y: int| NumbersInTree(new_right).contains(y) implies n < y by {
                        if NumbersInTree(*right).contains(y) {
                            assert(n < y);
                        } else {
                            assert(y == x);
                            assert(n < x);
                        }
                    }
                    assert(BST_property(result));
                    lemma_BST_equiv(result);
                }
                result
            }
        }
    }
}

proof fn lemma_numbers_in_sequence_subrange(q: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= q.len()
    ensures NumbersInSequence(q.subrange(i, j)) == 
            Set::new(|x: int| exists|k: int| i <= k < j && q[k] == x)
{
    // This follows from the definition of NumbersInSequence and subrange
}

proof fn lemma_numbers_in_sequence_extend(q: Seq<int>, i: int)
    requires 0 <= i < q.len()
    ensures NumbersInSequence(q.subrange(0, i + 1)) == 
            NumbersInSequence(q.subrange(0, i)).insert(q[i])
{
    lemma_numbers_in_sequence_subrange(q, 0, i);
    lemma_numbers_in_sequence_subrange(q, 0, i + 1);
}

fn BuildBST(q: Seq<int>) -> (t: Tree)
    requires NoDuplicates(q)
    ensures 
        BST(t),
        NumbersInTree(t) == NumbersInSequence(q)
{
    let mut result = Tree::Empty;
    let mut i = 0;
    
    while i < q.len()
        invariant
            0 <= i <= q.len(),
            BST(result),
            NumbersInTree(result) == NumbersInSequence(q.subrange(0, i)),
            forall|j: int, k: int| 0 <= j < k < i ==> q[j] != q[k]
    {
        proof {
            // Prove that q[i] is not already in the tree
            lemma_numbers_in_sequence_subrange(q, 0, i);
            
            assert forall|k: int| 0 <= k < i implies q[k] != q[i] by {
                if 0 <= k < i {
                    assert(0 <= k < i < q.len());
                    assert(q[k] != q[i]); // from NoDuplicates
                }
            }
            
            assert(!(NumbersInTree(result).contains(q[i])));
        }
        
        result = InsertBST(result, q[i]);
        
        proof {
            lemma_numbers_in_sequence_extend(q, i);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == q.len());
        assert(q.subrange(0, i) =~= q);
        lemma_numbers_in_sequence_subrange(q, 0, q.len());
    }
    
    result
}

fn PrintTreeNumbersInorder(t: Tree)
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            PrintTreeNumbersInorder(*left);
            print!("{} ", n);
            PrintTreeNumbersInorder(*right);
        }
    }
}

}