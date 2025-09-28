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
spec fn insert_bst_spec(t: Tree, x: int) -> Tree
    decreases t
{
    match t {
        Tree::Empty => Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty)),
        Tree::Node(n, left, right) => {
            if x < n {
                Tree::Node(n, Box::new(insert_bst_spec(*left, x)), right)
            } else {
                Tree::Node(n, left, Box::new(insert_bst_spec(*right, x)))
            }
        }
    }
}

proof fn lemma_insert_maintains_ascending(t: Tree, x: int)
    requires
        bst(t),
        !numbers_in_tree(t).contains(x),
    ensures
        ascending(inorder(insert_bst_spec(t, x))),
    decreases t,
{
    match t {
        Tree::Empty => {
            assert(inorder(insert_bst_spec(t, x)) == seq![x]);
            assert(ascending(seq![x]));
        }
        Tree::Node(n, left, right) => {
            if x < n {
                lemma_insert_maintains_ascending(*left, x);
                let result_inorder = inorder(insert_bst_spec(t, x));
                
                assert forall|i: int, j: int| 0 <= i < j < result_inorder.len() implies result_inorder[i] < result_inorder[j] by {
                    let left_result = insert_bst_spec(*left, x);
                    let left_len = inorder(left_result).len();
                    let mid_idx = left_len;
                    let right_start = left_len + 1;
                    
                    if j < left_len {
                        assert(ascending(inorder(left_result)));
                    } else if i < left_len && j == mid_idx {
                        assert(result_inorder[j] == n);
                        assert forall|k: int| 0 <= k < inorder(*left).len() implies inorder(*left)[k] < n by {
                            assert(bst(t));
                            assert(ascending(inorder(t)));
                        }
                        assert(result_inorder[i] < n);
                    } else if i < left_len && j >= right_start {
                        assert(result_inorder[i] < n);
                        assert(n < result_inorder[j]);
                    } else if i == mid_idx && j >= right_start {
                        assert(result_inorder[i] == n);
                        assert(n < result_inorder[j]);
                    } else if i >= right_start {
                        assert(ascending(inorder(*right)));
                    }
                }
            } else {
                lemma_insert_maintains_ascending(*right, x);
                let result_inorder = inorder(insert_bst_spec(t, x));
                
                assert forall|i: int, j: int| 0 <= i < j < result_inorder.len() implies result_inorder[i] < result_inorder[j] by {
                    let right_result = insert_bst_spec(*right, x);
                    let left_len = inorder(*left).len();
                    let mid_idx = left_len;
                    let right_start = left_len + 1;
                    
                    if j < left_len {
                        assert(ascending(inorder(*left)));
                    } else if i < left_len && j == mid_idx {
                        assert(result_inorder[j] == n);
                        assert(result_inorder[i] < n);
                    } else if i < left_len && j >= right_start {
                        assert(result_inorder[i] < n);
                        assert forall|k: int| 0 <= k < inorder(*right).len() implies n < inorder(*right)[k] by {
                            assert(bst(t));
                            assert(ascending(inorder(t)));
                        }
                        assert(n < result_inorder[j]);
                    } else if i == mid_idx && j >= right_start {
                        assert(result_inorder[i] == n);
                        assert(n < result_inorder[j]);
                    } else if i >= right_start {
                        assert(ascending(inorder(right_result)));
                    }
                }
            }
        }
    }
}

proof fn lemma_insert_adds_element(t: Tree, x: int)
    requires
        !numbers_in_tree(t).contains(x),
    ensures
        numbers_in_tree(insert_bst_spec(t, x)) =~= numbers_in_tree(t).insert(x),
    decreases t,
{
    match t {
        Tree::Empty => {
            assert(inorder(insert_bst_spec(t, x)) == seq![x]);
            assert(numbers_in_tree(insert_bst_spec(t, x)).contains(x));
            assert forall|y: int| numbers_in_tree(insert_bst_spec(t, x)).contains(y) <==> y == x by {
                assert(inorder(insert_bst_spec(t, x)) == seq![x]);
            }
        }
        Tree::Node(n, left, right) => {
            if x < n {
                lemma_insert_adds_element(*left, x);
                let left_result = insert_bst_spec(*left, x);
                assert(inorder(insert_bst_spec(t, x)) == inorder(left_result) + seq![n] + inorder(*right));
            } else {
                lemma_insert_adds_element(*right, x);
                let right_result = insert_bst_spec(*right, x);
                assert(inorder(insert_bst_spec(t, x)) == inorder(*left) + seq![n] + inorder(right_result));
            }
        }
    }
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
    decreases t0;
    let result = match t0 {
        Tree::Empty => {
            Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty))
        }
        Tree::Node(n, left, right) => {
            if x < n {
                let left_result = insert_bst(*left, x);
                Tree::Node(n, Box::new(left_result), right)
            } else {
                let right_result = insert_bst(*right, x);
                Tree::Node(n, left, Box::new(right_result))
            }
        }
    };
    
    proof {
        lemma_insert_maintains_ascending(t0, x);
        lemma_insert_adds_element(t0, x);
        assert(result == insert_bst_spec(t0, x)) by {
            match t0 {
                Tree::Empty => {}
                Tree::Node(n, left, right) => {
                    if x < n {
                        assert(result == Tree::Node(n, Box::new(insert_bst_spec(*left, x)), right));
                    } else {
                        assert(result == Tree::Node(n, left, Box::new(insert_bst_spec(*right, x))));
                    }
                }
            }
        }
        assert(bst(result));
        assert(numbers_in_tree(result) =~= numbers_in_tree(t0).insert(x));
    }
    
    result
}
// </vc-code>

fn main() {}

}