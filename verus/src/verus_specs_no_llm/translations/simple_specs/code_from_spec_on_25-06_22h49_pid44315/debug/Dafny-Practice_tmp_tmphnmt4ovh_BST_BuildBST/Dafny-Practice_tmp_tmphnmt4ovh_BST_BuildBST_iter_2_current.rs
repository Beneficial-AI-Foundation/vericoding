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

// Helper lemma to prove properties about NumbersInSequence
proof fn lemma_numbers_in_sequence_subrange(q: Seq<int>, i: int)
    requires 0 <= i <= q.len()
    ensures NumbersInSequence(q.subrange(0, i)).union(set![q[i]]) <= NumbersInSequence(q.subrange(0, i + 1))
    decreases q.len() - i
{
    if i < q.len() {
        assert(q.subrange(0, i + 1) == q.subrange(0, i).push(q[i]));
    }
}

// Helper lemma about NoDuplicates and subranges
proof fn lemma_no_duplicates_subrange(q: Seq<int>, i: int)
    requires 
        NoDuplicates(q),
        0 <= i <= q.len()
    ensures forall|j: int, k: int| 0 <= j < k < i ==> q[j] != q[k]
{
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
    assert(forall|j: int| 0 <= j < i ==> q[j] != q[i]) by {
        lemma_no_duplicates_subrange(q, i + 1);
    };
    
    // Therefore q[i] is not in NumbersInSequence(q.subrange(0, i))
    assert(!NumbersInSequence(q.subrange(0, i)).contains(q[i]));
    
    // And the union property holds
    assert(NumbersInSequence(q.subrange(0, i + 1)) == NumbersInSequence(q.subrange(0, i)).union(set![q[i]]));
}

fn InsertBST(t0: Tree, x: int) -> (t: Tree)
    requires 
        BST(t0),
        !NumbersInTree(t0).contains(x)
    ensures 
        BST(t),
        NumbersInTree(t) == NumbersInTree(t0).union(set![x])
{
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