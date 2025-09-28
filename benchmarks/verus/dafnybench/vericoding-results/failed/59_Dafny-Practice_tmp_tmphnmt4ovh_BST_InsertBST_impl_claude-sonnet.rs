use vstd::prelude::*;

verus! {

pub enum Tree {
    Empty,
    Node(int, Box<Tree>, Box<Tree>),
}

spec fn numbers_in_tree(t: Tree) -> Set<int> {
    numbers_in_sequence(inorder(t))
}

spec fn numbers_in_sequence(q: Seq<int>) -> Set<int> {
    Set::new(|x: int| q.contains(x))
}

spec fn bst(t: Tree) -> bool {
    ascending(inorder(t))
}

spec fn inorder(t: Tree) -> Seq<int>
    decreases t
{
    match t {
        Tree::Empty => seq![],
        Tree::Node(n, left, right) => inorder(*left) + seq![n] + inorder(*right)
    }
}

spec fn ascending(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] < q[j]
}

spec fn no_duplicates(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < q.len() ==> q[i] != q[j]
}

// <vc-helpers>
proof fn lemma_ascending_implies_no_duplicates(q: Seq<int>)
    requires ascending(q)
    ensures no_duplicates(q)
{
    assert forall|i: int, j: int| 0 <= i < j < q.len() implies q[i] != q[j] by {
        if 0 <= i < j < q.len() {
            assert(q[i] < q[j]);
        }
    }
}

proof fn lemma_inorder_insert_left(left: Tree, n: int, right: Tree, x: int, new_left: Tree)
    requires 
        bst(Tree::Node(n, Box::new(left), Box::new(right))),
        x < n,
        bst(new_left),
        numbers_in_tree(new_left) =~= numbers_in_tree(left).insert(x)
    ensures 
        bst(Tree::Node(n, Box::new(new_left), Box::new(right))),
        numbers_in_tree(Tree::Node(n, Box::new(new_left), Box::new(right))) =~= 
        numbers_in_tree(Tree::Node(n, Box::new(left), Box::new(right))).insert(x)
{
    let old_tree = Tree::Node(n, Box::new(left), Box::new(right));
    let new_tree = Tree::Node(n, Box::new(new_left), Box::new(right));
    
    assert(inorder(new_tree) =~= inorder(new_left) + seq![n] + inorder(right));
    assert(inorder(old_tree) =~= inorder(left) + seq![n] + inorder(right));
    
    lemma_ascending_implies_no_duplicates(inorder(old_tree));
    lemma_ascending_implies_no_duplicates(inorder(new_left));
    
    assert(ascending(inorder(new_tree))) by {
        let new_seq = inorder(new_tree);
        assert forall|i: int, j: int| 0 <= i < j < new_seq.len() implies new_seq[i] < new_seq[j] by {
            if 0 <= i < j < new_seq.len() {
                if i < inorder(new_left).len() && j < inorder(new_left).len() {
                    assert(new_seq[i] == inorder(new_left)[i]);
                    assert(new_seq[j] == inorder(new_left)[j]);
                } else if i < inorder(new_left).len() && j == inorder(new_left).len() {
                    assert(new_seq[i] == inorder(new_left)[i]);
                    assert(new_seq[j] == n);
                } else if i < inorder(new_left).len() && j > inorder(new_left).len() {
                    assert(new_seq[i] == inorder(new_left)[i]);
                    assert(new_seq[j] == inorder(right)[j - inorder(new_left).len() - 1]);
                } else if i == inorder(new_left).len() && j > inorder(new_left).len() {
                    assert(new_seq[i] == n);
                    assert(new_seq[j] == inorder(right)[j - inorder(new_left).len() - 1]);
                } else if i > inorder(new_left).len() && j > inorder(new_left).len() {
                    assert(new_seq[i] == inorder(right)[i - inorder(new_left).len() - 1]);
                    assert(new_seq[j] == inorder(right)[j - inorder(new_left).len() - 1]);
                }
            }
        }
    };
}

proof fn lemma_inorder_insert_right(left: Tree, n: int, right: Tree, x: int, new_right: Tree)
    requires 
        bst(Tree::Node(n, Box::new(left), Box::new(right))),
        x > n,
        bst(new_right),
        numbers_in_tree(new_right) =~= numbers_in_tree(right).insert(x)
    ensures 
        bst(Tree::Node(n, Box::new(left), Box::new(new_right))),
        numbers_in_tree(Tree::Node(n, Box::new(left), Box::new(new_right))) =~= 
        numbers_in_tree(Tree::Node(n, Box::new(left), Box::new(right))).insert(x)
{
    let old_tree = Tree::Node(n, Box::new(left), Box::new(right));
    let new_tree = Tree::Node(n, Box::new(left), Box::new(new_right));
    
    assert(inorder(new_tree) =~= inorder(left) + seq![n] + inorder(new_right));
    assert(inorder(old_tree) =~= inorder(left) + seq![n] + inorder(right));
    
    lemma_ascending_implies_no_duplicates(inorder(old_tree));
    lemma_ascending_implies_no_duplicates(inorder(new_right));
    
    assert(ascending(inorder(new_tree))) by {
        let new_seq = inorder(new_tree);
        assert forall|i: int, j: int| 0 <= i < j < new_seq.len() implies new_seq[i] < new_seq[j] by {
            if 0 <= i < j < new_seq.len() {
                if i < inorder(left).len() && j < inorder(left).len() {
                    assert(new_seq[i] == inorder(left)[i]);
                    assert(new_seq[j] == inorder(left)[j]);
                } else if i < inorder(left).len() && j == inorder(left).len() {
                    assert(new_seq[i] == inorder(left)[i]);
                    assert(new_seq[j] == n);
                } else if i < inorder(left).len() && j > inorder(left).len() {
                    assert(new_seq[i] == inorder(left)[i]);
                    assert(new_seq[j] == inorder(new_right)[j - inorder(left).len() - 1]);
                } else if i == inorder(left).len() && j > inorder(left).len() {
                    assert(new_seq[i] == n);
                    assert(new_seq[j] == inorder(new_right)[j - inorder(left).len() - 1]);
                } else if i > inorder(left).len() && j > inorder(left).len() {
                    assert(new_seq[i] == inorder(new_right)[i - inorder(left).len() - 1]);
                    assert(new_seq[j] == inorder(new_right)[j - inorder(left).len() - 1]);
                }
            }
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn insert_bst(t0: Tree, x: int) -> (t: Tree)
    requires 
        bst(t0) && !numbers_in_tree(t0).contains(x)
    ensures 
        bst(t) && numbers_in_tree(t) =~= numbers_in_tree(t0).insert(x)
// </vc-spec>
// <vc-code>
{
    match t0 {
        Tree::Empty => {
            let result = Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty));
            assert(inorder(result) =~= seq![x]);
            assert(ascending(inorder(result)));
            assert(numbers_in_tree(result) =~= numbers_in_tree(t0).insert(x));
            result
        },
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = insert_bst(*left, x);
                let result = Tree::Node(n, Box::new(new_left), right);
                proof {
                    lemma_inorder_insert_left(*left, n, *right, x, new_left);
                }
                result
            } else {
                let new_right = insert_bst(*right, x);
                let result = Tree::Node(n, left, Box::new(new_right));
                proof {
                    lemma_inorder_insert_right(*left, n, *right, x, new_right);
                }
                result
            }
        }
    }
}
// </vc-code>

fn main() {}

}