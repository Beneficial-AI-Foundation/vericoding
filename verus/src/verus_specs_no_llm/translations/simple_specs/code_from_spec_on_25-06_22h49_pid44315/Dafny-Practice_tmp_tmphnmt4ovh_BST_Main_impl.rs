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

// Key lemmas
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
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![n] + right_seq;
            
            assert forall|x: int| NumbersInTree(t).contains(x) implies 
                   exists|i: int| 0 <= i < full_seq.len() && full_seq[i] == x by {
                if NumbersInTree(*left).contains(x) {
                    let i_left = choose|i: int| 0 <= i < left_seq.len() && left_seq[i] == x;
                    assert(0 <= i_left < full_seq.len());
                    assert(full_seq[i_left] == x);
                } else if x == n {
                    let i_n = left_seq.len();
                    assert(0 <= i_n < full_seq.len());
                    assert(full_seq[i_n] == n);
                } else {
                    assert(NumbersInTree(*right).contains(x));
                    let i_right = choose|i: int| 0 <= i < right_seq.len() && right_seq[i] == x;
                    let i_full = left_seq.len() + 1 + i_right;
                    assert(0 <= i_full < full_seq.len());
                    assert(full_seq[i_full] == x);
                }
            }
        }
    }
}

proof fn lemma_tree_numbers_from_inorder(t: Tree)
    ensures forall|i: int| 0 <= i < Inorder(t).len() ==> 
            NumbersInTree(t).contains(Inorder(t)[i])
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_tree_numbers_from_inorder(*left);
            lemma_tree_numbers_from_inorder(*right);
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![n] + right_seq;
            
            assert forall|i: int| 0 <= i < full_seq.len() implies 
                   NumbersInTree(t).contains(full_seq[i]) by {
                if i < left_seq.len() {
                    assert(full_seq[i] == left_seq[i]);
                    assert(NumbersInTree(*left).contains(left_seq[i]));
                    assert(NumbersInTree(t).contains(full_seq[i]));
                } else if i == left_seq.len() {
                    assert(full_seq[i] == n);
                    assert(NumbersInTree(t).contains(n));
                } else {
                    let j = i - left_seq.len() - 1;
                    assert(0 <= j < right_seq.len());
                    assert(full_seq[i] == right_seq[j]);
                    assert(NumbersInTree(*right).contains(right_seq[j]));
                    assert(NumbersInTree(t).contains(full_seq[i]));
                }
            }
        }
    }
}

proof fn lemma_BST_equiv(t: Tree)
    ensures BST(t) <==> BST_property(t)
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_BST_equiv(*left);
            lemma_BST_equiv(*right);
            lemma_inorder_contains_tree_numbers(t);
            lemma_tree_numbers_from_inorder(t);
            
            if BST_property(t) {
                lemma_bst_property_implies_ascending(t);
            }
            if BST(t) {
                lemma_ascending_implies_bst_property(t);
            }
        }
    }
}

proof fn lemma_bst_property_implies_ascending(t: Tree)
    requires BST_property(t)
    ensures Ascending(Inorder(t))
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_bst_property_implies_ascending(*left);
            lemma_bst_property_implies_ascending(*right);
            lemma_tree_numbers_from_inorder(*left);
            lemma_tree_numbers_from_inorder(*right);
            
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![n] + right_seq;
            
            assert forall|i: int, j: int| 0 <= i < j < full_seq.len() implies full_seq[i] < full_seq[j] by {
                if j < left_seq.len() {
                    // Both in left subtree
                    assert(full_seq[i] == left_seq[i]);
                    assert(full_seq[j] == left_seq[j]);
                    assert(left_seq[i] < left_seq[j]);
                } else if i < left_seq.len() && j == left_seq.len() {
                    // i in left, j is root
                    assert(full_seq[i] == left_seq[i]);
                    assert(NumbersInTree(*left).contains(left_seq[i]));
                    assert(left_seq[i] < n);
                    assert(full_seq[j] == n);
                } else if i < left_seq.len() && j > left_seq.len() {
                    // i in left, j in right
                    let j_right = j - left_seq.len() - 1;
                    assert(0 <= j_right < right_seq.len());
                    assert(full_seq[i] == left_seq[i]);
                    assert(NumbersInTree(*left).contains(left_seq[i]));
                    assert(NumbersInTree(*right).contains(right_seq[j_right]));
                    assert(left_seq[i] < n);
                    assert(n < right_seq[j_right]);
                    assert(full_seq[j] == right_seq[j_right]);
                } else if i == left_seq.len() && j > left_seq.len() {
                    // i is root, j in right
                    let j_right = j - left_seq.len() - 1;
                    assert(0 <= j_right < right_seq.len());
                    assert(NumbersInTree(*right).contains(right_seq[j_right]));
                    assert(n < right_seq[j_right]);
                    assert(full_seq[i] == n);
                    assert(full_seq[j] == right_seq[j_right]);
                } else {
                    // Both in right subtree
                    let i_right = i - left_seq.len() - 1;
                    let j_right = j - left_seq.len() - 1;
                    assert(0 <= i_right < j_right < right_seq.len());
                    assert(right_seq[i_right] < right_seq[j_right]);
                    assert(full_seq[i] == right_seq[i_right]);
                    assert(full_seq[j] == right_seq[j_right]);
                }
            }
        }
    }
}

proof fn lemma_ascending_implies_bst_property(t: Tree)
    requires Ascending(Inorder(t))
    ensures BST_property(t)
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            let left_seq = Inorder(*left);
            let right_seq = Inorder(*right);
            let full_seq = left_seq + seq![n] + right_seq;
            
            // Extract ascending property for subtrees
            assert forall|i: int, j: int| 0 <= i < j < left_seq.len() implies left_seq[i] < left_seq[j] by {
                assert(0 <= i < j < full_seq.len());
                assert(full_seq[i] == left_seq[i]);
                assert(full_seq[j] == left_seq[j]);
                assert(full_seq[i] < full_seq[j]);
            }
            
            assert forall|i: int, j: int| 0 <= i < j < right_seq.len() implies right_seq[i] < right_seq[j] by {
                let full_i = left_seq.len() + 1 + i;
                let full_j = left_seq.len() + 1 + j;
                assert(0 <= full_i < full_j < full_seq.len());
                assert(full_seq[full_i] == right_seq[i]);
                assert(full_seq[full_j] == right_seq[j]);
                assert(full_seq[full_i] < full_seq[full_j]);
            }
            
            lemma_ascending_implies_bst_property(*left);
            lemma_ascending_implies_bst_property(*right);
            lemma_tree_numbers_from_inorder(*left);
            lemma_tree_numbers_from_inorder(*right);
            
            // Prove ordering constraints
            assert forall|x: int| NumbersInTree(*left).contains(x) implies x < n by {
                let i = choose|i: int| 0 <= i < left_seq.len() && left_seq[i] == x;
                assert(full_seq[i] == x);
                assert(full_seq[left_seq.len()] == n);
                assert(0 <= i < left_seq.len() < full_seq.len());
                assert(full_seq[i] < full_seq[left_seq.len()]);
                assert(x < n);
            }
            
            assert forall|x: int| NumbersInTree(*right).contains(x) implies n < x by {
                let i = choose|i: int| 0 <= i < right_seq.len() && right_seq[i] == x;
                let full_i = left_seq.len() + 1 + i;
                assert(full_seq[full_i] == x);
                assert(full_seq[left_seq.len()] == n);
                assert(0 <= left_seq.len() < full_i < full_seq.len());
                assert(full_seq[left_seq.len()] < full_seq[full_i]);
                assert(n < x);
            }
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
                    
                    assert(BST_property(*right));
                    assert(NumbersInTree(new_left) == NumbersInTree(*left).insert(x));
                    
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
                assert(x > n) by {
                    if x == n {
                        assert(NumbersInTree(t0).contains(x));
                        assert(false);
                    }
                }
                let new_right = InsertBST(*right, x);
                let result = Tree::Node(n, box *left, box new_right);
                proof {
                    lemma_BST_equiv(*left);
                    lemma_BST_equiv(*right);
                    lemma_BST_equiv(new_right);
                    
                    assert(BST_property(*left));
                    assert(NumbersInTree(new_right) == NumbersInTree(*right).insert(x));
                    assert(forall|y: int| NumbersInTree(*left).contains(y) ==> y < n);
                    
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
    let sub_seq = q.subrange(i, j);
    assert forall|x: int| NumbersInSequence(sub_seq).contains(x) <==> 
           Set::new(|x: int| exists|k: int| i <= k < j && q[k] == x).contains(x) by {
        if NumbersInSequence(sub_seq).contains(x) {
            let idx = choose|idx: int| 0 <= idx < sub_seq.len() && sub_seq[idx] == x;
            assert(q[i + idx] == x);
            assert(i <= i + idx < j);
        }
        if Set::new(|x: int| exists|k: int| i <= k < j && q[k] == x).contains(x) {
            let k = choose|k: int| i <= k < j && q[k] == x;
            assert(0 <= k - i < j - i);
            assert(sub_seq[k - i] == x);
            assert(0 <= k - i < sub_seq.len());
        }
    }
}

proof fn lemma_numbers_in_sequence_extend(q: Seq<int>, i: int)
    requires 0 <= i < q.len()
    ensures NumbersInSequence(q.subrange(0, i + 1)) == 
            NumbersInSequence(q.subrange(0, i)).insert(q[i])
{
    lemma_numbers_in_sequence_subrange(q, 0, i);
    lemma_numbers_in_sequence_subrange(q, 0, i + 1);
    
    assert forall|x: int| NumbersInSequence(q.subrange(0, i + 1)).contains(x) <==>
           NumbersInSequence(q.subrange(0, i)).insert(q[i]).contains(x) by {
        if NumbersInSequence(q.subrange(0, i + 1)).contains(x) {
            if exists|k: int| 0 <= k < i && q[k] == x {
                assert(NumbersInSequence(q.subrange(0, i)).contains(x));
            } else {
                assert(q[i] == x);
            }
        }
        if NumbersInSequence(q.subrange(0, i)).insert(q[i]).contains(x) {
            if NumbersInSequence(q.subrange(0, i)).contains(x) {
                assert(exists|k: int| 0 <= k < i && q[k] == x);
                assert(exists|k: int| 0 <= k < i + 1 && q[k] == x);
            } else {
                assert(x == q[i]);
                assert(exists|k: int| 0 <= k < i + 1 && q[k] == x);
            }
        }
    }
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
            NoDuplicates(q)
    {
        proof {
            lemma_numbers_in_sequence_subrange(q, 0, i);
            
            assert(!(NumbersInTree(result).contains(q[i]))) by {
                if NumbersInTree(result).contains(q[i]) {
                    let k = choose|k: int| 0 <= k < i && q[k] == q[i];
                    assert(0 <= k < i < q.len());
                    assert(k != i);
                    if k < i {
                        assert(q[k] != q[i]); // from NoDuplicates
                    } else {
                        assert(q[i] != q[k]); // from NoDuplicates
                    }
                    assert(false);
                }
            }
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
        assert(NumbersInSequence(q.subrange(0, q.len())) == NumbersInSequence(q));
    }
    
    result
}

fn PrintTreeNumbersInorder(t: Tree)
{
    match t {
        Tree::Empty => {},
        Tree::Node(_, left, right) => {
            PrintTreeNumbersInorder(*left);
            // Note: print! is not available in Verus verification mode
            // This would need to be handled differently in a real implementation
            PrintTreeNumbersInorder(*right);
        }
    }
}

}