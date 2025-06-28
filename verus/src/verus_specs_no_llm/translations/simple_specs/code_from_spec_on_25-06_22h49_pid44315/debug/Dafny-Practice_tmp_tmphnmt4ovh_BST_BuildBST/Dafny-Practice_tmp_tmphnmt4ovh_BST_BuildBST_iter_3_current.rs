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
            lemma_inorder_numbers_match(*left);
            lemma_inorder_numbers_match(*right);
            lemma_numbers_in_sequence_concatenation(Inorder(*left), seq![n], Inorder(*right));
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
            let i = choose|i: int| 0 <= i < combined.len() && combined[i] == x;
            if i < s1.len() {
                assert(NumbersInSequence(s1).contains(x));
            } else if i < s1.len() + s2.len() {
                assert(NumbersInSequence(s2).contains(x));
            } else {
                assert(NumbersInSequence(s3).contains(x));
            }
        }
        if NumbersInSequence(s1).contains(x) {
            let i = choose|i: int| 0 <= i < s1.len() && s1[i] == x;
            assert(combined[i] == x);
        }
        if NumbersInSequence(s2).contains(x) {
            let i = choose|i: int| 0 <= i < s2.len() && s2[i] == x;
            assert(combined[s1.len() + i] == x);
        }
        if NumbersInSequence(s3).contains(x) {
            let i = choose|i: int| 0 <= i < s3.len() && s3[i] == x;
            assert(combined[s1.len() + s2.len() + i] == x);
        }
    }
}

// Helper lemma about BST insertion preserving order
proof fn lemma_insert_preserves_bst(t: Tree, x: int)
    requires 
        BST(t),
        !NumbersInTree(t).contains(x)
    ensures BST(InsertBST(t, x))
    decreases t
{
    match t {
        Tree::Empty => {},
        Tree::Node(n, left, right) => {
            if x < n {
                lemma_insert_preserves_bst(*left, x);
                lemma_insert_left_preserves_order(*left, *right, n, x);
            } else {
                lemma_insert_preserves_bst(*right, x);
                lemma_insert_right_preserves_order(*left, *right, n, x);
            }
        }
    }
}

// Helper lemma for left insertion
proof fn lemma_insert_left_preserves_order(left: Tree, right: Tree, n: int, x: int)
    requires 
        BST(Tree::Node(n, box left, box right)),
        !NumbersInTree(Tree::Node(n, box left, box right)).contains(x),
        x < n,
        BST(InsertBST(left, x))
    ensures BST(Tree::Node(n, box InsertBST(left, x), box right))
{
    let new_tree = Tree::Node(n, box InsertBST(left, x), box right);
    let inorder = Inorder(new_tree);
    
    assert(Ascending(inorder)) by {
        let left_inorder = Inorder(InsertBST(left, x));
        let right_inorder = Inorder(right);
        assert(inorder == left_inorder + seq![n] + right_inorder);
        assert(Ascending(left_inorder));
        assert(Ascending(right_inorder));
        
        // All elements in left are < n, and x < n, so all elements in new left are < n
        assert(forall|i: int| 0 <= i < left_inorder.len() ==> left_inorder[i] < n);
        // All elements in right are > n  
        assert(forall|i: int| 0 <= i < right_inorder.len() ==> right_inorder[i] > n);
    }
}

// Helper lemma for right insertion  
proof fn lemma_insert_right_preserves_order(left: Tree, right: Tree, n: int, x: int)
    requires 
        BST(Tree::Node(n, box left, box right)),
        !NumbersInTree(Tree::Node(n, box left, box right)).contains(x),
        x >= n,
        BST(InsertBST(right, x))
    ensures BST(Tree::Node(n, box left, box InsertBST(right, x)))
{
    let new_tree = Tree::Node(n, box left, box InsertBST(right, x));
    let inorder = Inorder(new_tree);
    
    assert(Ascending(inorder)) by {
        let left_inorder = Inorder(left);
        let right_inorder = Inorder(InsertBST(right, x));
        assert(inorder == left_inorder + seq![n] + right_inorder);
        assert(Ascending(left_inorder));
        assert(Ascending(right_inorder));
        
        // All elements in left are < n
        assert(forall|i: int| 0 <= i < left_inorder.len() ==> left_inorder[i] < n);
        // All elements in right are > n, and x >= n
        assert(forall|i: int| 0 <= i < right_inorder.len() ==> right_inorder[i] > n);
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
            let k = choose|k: int| 0 <= k < sub.len() && sub[k] == x;
            if k < i {
                assert(NumbersInSequence(q.subrange(0, i)).contains(x));
            } else {
                assert(k == i && x == q[i]);
            }
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
{
    proof {
        lemma_insert_preserves_bst(t0, x);
    }
    
    match t0 {
        Tree::Empty => Tree::Node(x, box Tree::Empty, box Tree::Empty),
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = InsertBST(*left, x);
                Tree::Node(n, box new_left, right)
            } else {
                let new_right = InsertBST(*right, x);
                Tree::Node(n, left, box new_right)
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
    assert(q.subrange(0, q.len()) == q);
    
    result
}

}