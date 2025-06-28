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
        
        if NumbersInSequence(s3).contains(x) {
            let i = choose|i: int| 0 <= i < s3.len() && s3[i] == x;
            assert(combined[s1.len() + s2.len() + i] == x);
            assert(NumbersInSequence(combined).contains(x));
        }
    }
}

// Helper lemma about BST ordering properties
proof fn lemma_bst_ordering_left(t: Tree, x: int)
    requires BST(t)
    ensures forall|y: int| NumbersInTree(t).contains(y) ==> y < x
{
    lemma_inorder_numbers_match(t);
}

proof fn lemma_bst_ordering_right(t: Tree, x: int)
    requires BST(t)
    ensures forall|y: int| NumbersInTree(t).contains(y) ==> y > x
{
    lemma_inorder_numbers_match(t);
}

// Helper lemma to prove BST property is maintained after insertion
proof fn lemma_insert_maintains_bst(left: Tree, n: int, right: Tree, new_subtree: Tree, is_left: bool)
    requires 
        BST(Tree::Node(n, Box::new(left), Box::new(right))),
        BST(new_subtree),
        is_left ==> (forall|y: int| NumbersInTree(new_subtree).contains(y) ==> y < n),
        !is_left ==> (forall|y: int| NumbersInTree(new_subtree).contains(y) ==> y > n)
    ensures 
        is_left ==> BST(Tree::Node(n, Box::new(new_subtree), Box::new(right))),
        !is_left ==> BST(Tree::Node(n, Box::new(left), Box::new(new_subtree)))
{
    if is_left {
        let new_tree = Tree::Node(n, Box::new(new_subtree), Box::new(right));
        lemma_inorder_numbers_match(new_subtree);
        lemma_inorder_numbers_match(right);
        lemma_inorder_numbers_match(new_tree);
    } else {
        let new_tree = Tree::Node(n, Box::new(left), Box::new(new_subtree));
        lemma_inorder_numbers_match(left);
        lemma_inorder_numbers_match(new_subtree);
        lemma_inorder_numbers_match(new_tree);
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
                    lemma_bst_ordering_left(*left, n);
                    lemma_bst_ordering_right(*right, n);
                    lemma_insert_maintains_bst(*left, n, *right, new_left, true);
                }
                
                Tree::Node(n, Box::new(new_left), right)
            } else {
                let new_right = InsertBST(*right, x);
                
                proof {
                    lemma_bst_ordering_left(*left, n);
                    lemma_bst_ordering_right(*right, n);
                    lemma_insert_maintains_bst(*left, n, *right, new_right, false);
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