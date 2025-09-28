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
spec fn insert_seq(q: Seq<int>, x: int) -> Seq<int>
    decreases q.len()
{
    if q.len() == 0 {
        seq![x]
    } else {
        let h = q[0];
        let t = q.slice(1, q.len());
        if x < h {
            seq![x] + q
        } else {
            seq![h] + insert_seq(t, x)
        }
    }
}

proof fn insert_seq_preserves_sorted(q: Seq<int>, x: int)
    requires
        ascending(q) && !q.contains(x)
    ensures
        ascending(insert_seq(q, x))
    decreases q.len()
{
    if q.len() == 0 {
        // trivial
    } else {
        let h = q[0];
        let t = q.slice(1, q.len());
        if x < h {
            // insert_seq(q,x) = [x] + q
            // Since x < h and q ascending, result ascending
        } else {
            // insert_seq(q,x) = [h] + insert_seq(t,x)
            insert_seq_preserves_sorted(t, x);
            // Need to show h < all elements of insert_seq(t,x).
            // From ascending(q) we know h < all elements of t.
            // Also x >= h, so h < x or h == x (but x not in q so h < x).
            // Therefore h < all elements of insert_seq(t,x).
        }
    }
}

proof fn insert_seq_sets(q: Seq<int>, x: int)
    requires
        !q.contains(x)
    ensures
        numbers_in_sequence(insert_seq(q, x)) =~= numbers_in_sequence(q).insert(x)
    decreases q.len()
{
    if q.len() == 0 {
        // insert_seq([], x) = [x]
    } else {
        let h = q[0];
        let t = q.slice(1, q.len());
        if x < h {
            // insert_seq(q,x) = [x] + q
        } else {
            // insert_seq(q,x) = [h] + insert_seq(t,x)
            insert_seq_sets(t, x);
        }
    }
}

proof fn ascending_split(qL: Seq<int>, n: int, qR: Seq<int>)
    requires
        ascending(qL + seq![n] + qR)
    ensures
        ascending(qL) && ascending(qR) &&
        (forall|i: int| 0 <= i < qL.len() ==> qL[i] < n) &&
        (forall|i: int| 0 <= i < qR.len() ==> n < qR[i])
{
    // automatic from unfolding definitions
}

proof fn insert_seq_dist_left(qL: Seq<int>, n: int, qR: Seq<int>, x: int)
    requires
        ascending(qL + seq![n] + qR) &&
        x < n &&
        !(qL + seq![n] + qR).contains(x)
    ensures
        insert_seq(qL + seq![n] + qR, x) == insert_seq(qL, x) + seq![n] + qR
    decreases qL.len()
{
    if qL.len() == 0 {
        // qL = []
        // lhs = insert_seq([n] + qR, x)
        // since x < n, lhs = [x] + [n] + qR
        // rhs = insert_seq([], x) + [n] + qR = [x] + [n] + qR
    } else {
        let h = qL[0];
        let t = qL.slice(1, qL.len());
        ascending_split(qL, n, qR);
        if x < h {
            // insertion before h, straightforward
        } else {
            // x >= h
            // lhs = [h] + insert_seq(t + seq![n] + qR, x)
            // rhs = [h] + insert_seq(t, x) + seq![n] + qR
            insert_seq_dist_left(t, n, qR, x);
            // conclude lhs == rhs
        }
    }
}

proof fn insert_seq_dist_right(qL: Seq<int>, n: int, qR: Seq<int>, x: int)
    requires
        ascending(qL + seq![n] + qR) &&
        x > n &&
        !(qL + seq![n] + qR).contains(x)
    ensures
        insert_seq(qL + seq![n] + qR, x) == qL + seq![n] + insert_seq(qR, x)
    decreases qR.len()
{
    if qR.len() == 0 {
        // qR = []
        // lhs = insert_seq(qL + [n], x) with x > n -> qL + [n] + [x]
        // rhs = qL + [n] + insert_seq([], x) = qL + [n] + [x]
    } else {
        let h = qR[0];
        let t = qR.slice(1, qR.len());
        ascending_split(qL, n, qR);
        if x < h {
            // insertion happens at front of qR:
            // lhs = insert_seq(qL + [n] + [h] + t, x) = qL + [n] + [x] + [h] + t
            // rhs = qL + [n] + insert_seq([h] + t, x) = qL + [n] + [x] + [h] + t
        } else {
            // x >= h
            // insert_seq(qL + [n] + [h] + t, x) = qL + [n] + [h] + insert_seq(t,x)
            // and insert_seq([h] + t, x) = [h] + insert_seq(t,x)
            // therefore rhs = qL + [n] + [h] + insert_seq(t,x) = lhs
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
    match t0 {
        Tree::Empty => {
            let t = Tree::Node(x, Box::new(Tree::Empty), Box::new(Tree::Empty));
            proof {
                // inorder(t0) empty
                assert(inorder(t0).len() == 0);
                // inorder(t) = [x]
                assert(inorder(t).len() == 1);
                assert(inorder(t)[0] == x);
                // insert_seq([], x) = [x]
                assert(insert_seq(inorder(t0), x).len() == 1);
                assert(insert_seq(inorder(t0), x)[0] == x);
                // conclude inorder(t) == insert_seq(inorder(t0), x)
                assert(inorder(t) == insert_seq(inorder(t0), x));
            }
            t
        }
        Tree::Node(n, left, right) => {
            if x < n {
                let new_left = Box::new(insert_bst(*left, x));
                let t = Tree::Node(n, new_left, right);
                proof {
                    // By recursive call: inorder(*new_left) == insert_seq(inorder(*left), x)
                    assert(inorder(t) == inorder(*new_left) + seq![n] + inorder(*right));
                    assert(inorder(t0) == inorder(*left) + seq![n] + inorder(*right));
                    insert_seq_dist_left(inorder(*left), n, inorder(*right), x);
                    // use recursive equality
                    assert(inorder(*new_left) == insert_seq(inorder(*left), x));
                    assert(inorder(t) == insert_seq(inorder(*left), x) + seq![n] + inorder(*right));
                    assert(insert_seq(inorder(t0), x) == insert_seq(inorder(*left) + seq![n] + inorder(*right), x));
                    assert(inorder(t) == insert_seq(inorder(t0), x));
                }
                t
            } else {
                // x > n (precondition disallows equality)
                let new_right = Box::new(insert_bst(*right, x));
                let t = Tree::Node(n, left, new_right);
                proof {
                    assert(inorder(t) == inorder(*left) + seq![n] + inorder(*new_right));
                    assert(inorder(t0) == inorder(*left) + seq![n] + inorder(*right));
                    insert_seq_dist_right(inorder(*left), n, inorder(*right), x);
                    assert(inorder(t) == inorder(*left) + seq![n] + insert_seq(inorder(*right), x));
                    assert(insert_seq(inorder(t0), x) == inorder(*left) + seq![n] + insert_seq(inorder(*right), x));
                    assert(inorder(t) == insert_seq(inorder(t0), x));
                }
                t
            }
        }
    }
}
// </vc-code>

fn main() {}

}