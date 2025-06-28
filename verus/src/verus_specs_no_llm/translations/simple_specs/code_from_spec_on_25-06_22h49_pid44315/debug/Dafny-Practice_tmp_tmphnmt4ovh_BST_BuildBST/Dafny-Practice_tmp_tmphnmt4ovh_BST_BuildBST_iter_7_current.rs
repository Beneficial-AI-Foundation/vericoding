use builtin::*;
use builtin_macros::*;

verus! {

// Define the Tree datatype
pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

fn main() {
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

spec fn BST(t: Tree) -> bool {
    Ascending(Inorder(t))
}

// Helper lemma to establish the connection between Inorder and NumbersInTree
proof fn lemma_inorder_numbers_match(t: Tree)
    ensures NumbersInTree(t) == NumbersInSequence(Inorder(t))
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            lemma_inorder_numbers_match(**left);
            lemma_inorder_numbers_match(**right);
            lemma_numbers_in_sequence_concatenation(Inorder(**left), seq![n], Inorder(**right));
        }
    }
}

// Helper lemma about concatenation of sequences and their number sets
proof fn lemma_numbers_in_sequence_concatenation(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>)
    ensures NumbersInSequence(s1 + s2 + s3) == NumbersInSequence(s1).union(NumbersInSequence(s2)).union(NumbersInSequence(s3))
{
    let combined = s1 + s2 + s3;
    
    assert forall|x: int| NumbersInSequence(combined).contains(x) <==> 
        (NumbersInSequence(s1).union(NumbersInSequence(s2)).union(NumbersInSequence(s3))).contains(x) by {
        
        if NumbersInSequence(combined).contains(x) {
            assert(exists|i: int| 0 <= i < combined.len() && combined[i] == x);
            let i = choose|i: int| 0 <= i < combined.len() && combined[i] == x;
            
            if i < s1.len() {
                assert(combined[i] == s1[i]);
                assert(NumbersInSequence(s1).contains(x));
            } else if i < s1.len() + s2.len() {
                assert(combined[i] == s2[i - s1.len()]);
                assert(NumbersInSequence(s2).contains(x));
            } else {
                assert(combined[i] == s3[i - s1.len() - s2.len()]);
                assert(NumbersInSequence(s3).contains(x));
            }
        }
        
        if NumbersInSequence(s1).contains(x) {
            let i = choose|i: int| 0 <= i < s1.len() && s1[i] == x;
            assert(combined[i] == x);
            assert(NumbersInSequence(combined).contains(x));
        }
        
        if NumbersInSequence(s2).contains(x) {
            let i = choose|i: int| 0 <= i < s2.len() && s2[i] == x;
            assert(combined[s1.len() + i] == x);
            assert(NumbersInSequence(combined).contains(x));
        }
        
        if NumbersInSequence(s3).contains (x) {
            let i = choose|i: int| 0 <= i < s3.len() && s3[i] == x;
            assert(combined[s1.len() + s2.len() + i] == x);
            assert(NumbersInSequence(combined).contains(x));
        }
    }
}

// Helper lemma about BST ordering properties for left subtree
proof fn lemma_bst_ordering_left(left: Tree, n: int, right: Tree)
    requires BST(Tree::Node(n, Box::new(left), Box::new(right)))
    ensures forall|y: int| NumbersInTree(left).contains(y) ==> y < n
{
    lemma_inorder_numbers_match(left);
    lemma_inorder_numbers_match(right);
    lemma_inorder_numbers_match(Tree::Node(n, Box::new(left), Box::new(right)));
    
    let inorder_seq = Inorder(Tree::Node(n, Box::new(left), Box::new(right)));
    let left_seq = Inorder(left);
    
    assert forall|y: int| NumbersInTree(left).contains(y) ==> y < n by {
        if NumbersInTree(left).contains(y) {
            assert(NumbersInSequence(left_seq).contains(y));
            let i = choose|i: int| 0 <= i < left_seq.len() && left_seq[i] == y;
            // y appears at position i in the left subtree's inorder
            // In the full inorder sequence, this corresponds to position i
            assert(inorder_seq[i] == y);
            // The node value n appears at position left_seq.len() in the full sequence
            assert(inorder_seq[left_seq.len()] == n);
            // Since the sequence is ascending and i < left_seq.len()
            assert(i < left_seq.len());
            assert(y < n);
        }
    }
}

// Helper lemma about BST ordering properties for right subtree
proof fn lemma_bst_ordering_right(left: Tree, n: int, right: Tree)
    requires BST(Tree::Node(n, Box::new(left), Box::new(right)))
    ensures forall|y: int| NumbersInTree(right).contains(y) ==> y > n
{
    lemma_inorder_numbers_match(left);
    lemma_inorder_numbers_match(right);
    lemma_inorder_numbers_match(Tree::Node(n, Box::new(left), Box::new(right)));
    
    let inorder_seq = Inorder(Tree::Node(n, Box::new(left), Box::new(right)));
    let left_seq = Inorder(left);
    let right_seq = Inorder(right);
    
    assert forall|y: int| NumbersInTree(right).contains(y) ==> y > n by {
        if NumbersInTree(right).contains(y) {
            assert(NumbersInSequence(right_seq).contains(y));
            let i = choose|i: int| 0 <= i < right_seq.len() && right_seq[i] == y;
            // y appears at position i in the right subtree's inorder
            // In the full inorder sequence, this corresponds to position left_seq.len() + 1 + i
            let full_pos = left_seq.len() + 1 + i;
            assert(inorder_seq[full_pos] == y);
            // The node value n appears at position left_seq.len() in the full sequence
            assert(inorder_seq[left_seq.len()] == n);
            // Since the sequence is ascending and left_seq.len() < full_pos
            assert(left_seq.len() < full_pos);
            assert(n < y);
        }
    }
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires 
        BST(t0),
        !NumbersInTree(t0).contains(x)
    ensures 
        BST(t),
        NumbersInTree(t) == NumbersInTree(t0).union(set![x])
    decreases t0
{
    match t0 {
        Tree::Empty => {
            Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty))
        },
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = InsertBST(*left, x);
                
                proof {
                    lemma_bst_ordering_left(*left, n, *right);
                    lemma_bst_ordering_right(*left, n, *right);
                    
                    // Prove that new_left maintains the BST property with n and right
                    assert(BST(new_left));
                    assert(NumbersInTree(new_left) == NumbersInTree(*left).union(set![x]));
                    assert(x < n);
                    
                    assert forall|y: int| NumbersInTree(new_left).contains(y) ==> y < n by {
                        if NumbersInTree(new_left).contains(y) {
                            if NumbersInTree(*left).contains(y) {
                                assert(y < n);
                            } else {
                                assert(y == x);
                                assert(y < n);
                            }
                        }
                    }
                    
                    // Use inorder properties to prove BST
                    lemma_inorder_numbers_match(new_left);
                    lemma_inorder_numbers_match(*right);
                    lemma_inorder_numbers_match(Tree::Node(n, Box::new(new_left), Box::new(*right)));
                }
                
                Tree::Node(n, Box::new(new_left), right)
            } else {
                let new_right = InsertBST(*right, x);
                
                proof {
                    lemma_bst_ordering_left(*left, n, *right);
                    lemma_bst_ordering_right(*left, n, *right);
                    
                    // Prove that new_right maintains the BST property with left and n
                    assert(BST(new_right));
                    assert(NumbersInTree(new_right) == NumbersInTree(*right).union(set![x]));
                    assert(x > n);
                    
                    assert forall|y: int| NumbersInTree(new_right).contains(y) ==> y > n by {
                        if NumbersInTree(new_right).contains(y) {
                            if NumbersInTree(*right).contains(y) {
                                assert(y > n);
                            } else {
                                assert(y == x);
                                assert(y > n);
                            }
                        }
                    }
                    
                    // Use inorder properties to prove BST
                    lemma_inorder_numbers_match(*left);
                    lemma_inorder_numbers_match(new_right);
                    lemma_inorder_numbers_match(Tree::Node(n, Box::new(*left), Box::new(new_right)));
                }
                
                Tree::Node(n, left, Box::new(new_right))
            }
        }
    }
}

// Helper lemma about NumbersInSequence and subranges
proof fn lemma_numbers_in_sequence_extend(q: Seq<int>, i: int)
    requires 
        0 <= i < q.len(),
        NoDuplicates(q)
    ensures 
        !NumbersInSequence(q.subrange(0, i)).contains(q[i]),
        NumbersInSequence(q.subrange(0, i + 1)) == NumbersInSequence(q.subrange(0, i)).union(set![q[i]])
{
    // The element q[i] is not in the previous elements due to NoDuplicates
    assert(!NumbersInSequence(q.subrange(0, i)).contains(q[i])) by {
        if NumbersInSequence(q.subrange(0, i)).contains(q[i]) {
            assert(exists|j: int| 0 <= j < i && q.subrange(0, i)[j] == q[i]);
            let j = choose|j: int| 0 <= j < i && q.subrange(0, i)[j] == q[i];
            assert(q[j] == q[i] && j < i);
            assert(false); // Contradicts NoDuplicates
        }
    };
    
    // Prove the union property
    assert forall|x: int| NumbersInSequence(q.subrange(0, i + 1)).contains(x) <==> 
        NumbersInSequence(q.subrange(0, i)).union(set![q[i]]).contains(x) by {
        
        let sub = q.subrange(0, i + 1);
        
        if NumbersInSequence(sub).contains(x) {
            assert(exists|k: int| 0 <= k < sub.len() && sub[k] == x);
            let k = choose|k: int| 0 <= k < sub.len() && sub[k] == x;
            if k < i {
                assert(NumbersInSequence(q.subrange(0, i)).contains(x));
            } else {
                assert(k == i && x == q[i]);
            }
        }
        
        if NumbersInSequence(q.subrange(0, i)).contains(x) {
            assert(exists|k: int| 0 <= k < q.subrange(0, i).len() && q.subrange(0, i)[k] == x);
            let k = choose|k: int| 0 <= k < q.subrange(0, i).len() && q.subrange(0, i)[k] == x;
            assert(sub[k] == x);
            assert(NumbersInSequence(sub).contains(x));
        }
        
        if x == q[i] {
            assert(sub[i] == x);
            assert(NumbersInSequence(sub).contains(x));
        }
    }
}

// Helper lemma for subrange equality
proof fn lemma_subrange_full(q: Seq<int>)
    ensures q.subrange(0, q.len() as int) =~= q
{
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
            NumbersInTree(result) == NumbersInSequence(q.subrange(0, i))
    {
        proof {
            lemma_numbers_in_sequence_extend(q, i);
        }
        
        // Due to NoDuplicates, q[i] is not already in the tree
        assert(!NumbersInTree(result).contains(q[i]));
        
        result = InsertBST(result, q[i]);
        i = i + 1;
    }
    
    // At the end, q.subrange(0, q.len()) == q
    proof {
        lemma_subrange_full(q);
        assert(NumbersInTree(result) == NumbersInSequence(q.subrange(0, q.len() as int)));
        assert(NumbersInTree(result) == NumbersInSequence(q));
    }
    
    result
}

}