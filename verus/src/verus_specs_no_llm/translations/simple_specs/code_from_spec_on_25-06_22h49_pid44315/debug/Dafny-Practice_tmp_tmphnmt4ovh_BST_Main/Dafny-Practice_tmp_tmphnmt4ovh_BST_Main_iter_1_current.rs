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

// Helper lemma for insertion
proof fn lemma_insert_preserves_ascending(left_seq: Seq<int>, x: int, right_seq: Seq<int>)
    requires
        Ascending(left_seq),
        Ascending(right_seq),
        forall|i: int| 0 <= i < left_seq.len() ==> left_seq[i] < x,
        forall|i: int| 0 <= i < right_seq.len() ==> x < right_seq[i]
    ensures
        Ascending(left_seq + seq![x] + right_seq)
{
    let combined = left_seq + seq![x] + right_seq;
    assert forall|i: int, j: int| 0 <= i < j < combined.len() implies combined[i] < combined[j] by {
        if j < left_seq.len() {
            // Both indices in left part
            assert(combined[i] == left_seq[i]);
            assert(combined[j] == left_seq[j]);
        } else if i < left_seq.len() && j == left_seq.len() {
            // i in left, j is x
            assert(combined[i] == left_seq[i]);
            assert(combined[j] == x);
        } else if i < left_seq.len() && j > left_seq.len() {
            // i in left, j in right
            assert(combined[i] == left_seq[i]);
            assert(combined[j] == right_seq[j - left_seq.len() - 1]);
        } else if i == left_seq.len() && j > left_seq.len() {
            // i is x, j in right
            assert(combined[i] == x);
            assert(combined[j] == right_seq[j - left_seq.len() - 1]);
        } else {
            // Both in right part
            assert(combined[i] == right_seq[i - left_seq.len() - 1]);
            assert(combined[j] == right_seq[j - left_seq.len() - 1]);
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
    match t0 {
        Tree::Empty => {
            let result = Tree::Node(x, box Tree::Empty, box Tree::Empty);
            proof {
                assert(Inorder(result) == seq![x]);
                assert(Ascending(seq![x]));
            }
            result
        },
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = InsertBST(*left, x);
                let result = Tree::Node(n, box new_left, box *right);
                proof {
                    let left_seq = Inorder(*left);
                    let right_seq = Inorder(*right);
                    let new_left_seq = Inorder(new_left);
                    
                    assert(BST(*left) && BST(*right));
                    assert(forall|i: int| 0 <= i < left_seq.len() ==> left_seq[i] < n);
                    assert(forall|i: int| 0 <= i < right_seq.len() ==> n < right_seq[i]);
                    
                    lemma_insert_preserves_ascending(new_left_seq, n, right_seq);
                }
                result
            } else {
                let new_right = InsertBST(*right, x);
                let result = Tree::Node(n, box *left, box new_right);
                proof {
                    let left_seq = Inorder(*left);
                    let right_seq = Inorder(*right);
                    let new_right_seq = Inorder(new_right);
                    
                    assert(BST(*left) && BST(*right));
                    assert(forall|i: int| 0 <= i < left_seq.len() ==> left_seq[i] < n);
                    assert(forall|i: int| 0 <= i < right_seq.len() ==> n < right_seq[i]);
                    
                    lemma_insert_preserves_ascending(left_seq, n, new_right_seq);
                }
                result
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
            forall|j: int, k: int| 0 <= j < k < i ==> q[j] != q[k]
    {
        proof {
            assert(!(NumbersInTree(result).contains(q[i])));
        }
        result = InsertBST(result, q[i]);
        i = i + 1;
    }
    
    proof {
        assert(q.subrange(0, i) == q);
        assert(NumbersInSequence(q.subrange(0, i)) == NumbersInSequence(q));
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