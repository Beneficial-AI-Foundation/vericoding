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
lemma inorder_ascending_is_bst(t: Tree)
    requires bst(t)
    ensures ascending(inorder(t))
{
    open bst(t);
    match t {
        Tree::Empty => {
            assert(ascending(seq![]));
        }
        Tree::Node(_, left, right) => {
            inorder_ascending_is_bst(*left);
            inorder_ascending_is_bst(*right);
            assert(ascending(inorder(*left)));
            assert(ascending(inorder(*right)));
            assert forall|k: int, l: int| 0 <= k < l < inorder(*left).len() implies #[trigger] inorder(*left)[k] < inorder(*left)[l] by {
            }
            assert forall|k: int, l: int| 0 <= k < l < inorder(*right).len() implies #[trigger] inorder(*right)[k] < inorder(*right)[l] by {
            }
            if inorder(*left).len() > 0 && inorder(*right).len() > 0 {
                assert(inorder(*left)[inorder(*left).len()-1] < inorder(*right)[0]);
            } else if inorder(*left).len() > 0 {
                assert forall|i: int| 0 <= i < inorder(*left).len() implies #[trigger] inorder(*left)[i] < inorder(*right)[0] by {
                }
            }
        }
    }
}

lemma numbers_in_tree_is_set(t: Tree)
    ensures forall|x: int| #![auto] x in numbers_in_tree(t) <==> inorder(t).contains(x)
{
    match t {
        Tree::Empty => {
            assert forall|x: int| #![auto] x in numbers_in_tree(t) <==> inorder(t).contains(x) by {
                assert(numbers_in_tree(t) =~= Set::empty());
                assert(inorder(t) =~= seq![]);
            }
        }
        Tree::Node(_, _, _) => {
            let inorder_seq = inorder(t);
            let numbers_in_tree_set = numbers_in_tree(t);
            assert forall|x: int| #![auto] x in numbers_in_tree_set <==> inorder_seq.contains(x) by {
                assert(numbers_in_tree_set =~= numbers_in_sequence(inorder(*t.left).insert(t.value).union(numbers_in_sequence(inorder(*t.right)))));
            }
        }
    }
}

lemma inorder_insert_increases_left(t: Tree, x: int)
    requires
        bst(t),
        x < t.value,
    ensures
        inorder(insert_bst(t, x)) =~= inorder(insert_bst(*t.left, x)) + seq![t.value] + inorder(*t.right)
{
    open bst(t);
    match t {
        Tree::Node(_, left, right) => {
            inorder_insert_increases_left(*left, x);
            assert(inorder(t) =~= inorder(*left) + seq![t.value] + inorder(*right));
        }
        Tree::Empty => {}
    }
}

lemma inorder_insert_increases_right(t: Tree, x: int)
    requires
        bst(t),
        t.value < x,
    ensures
        inorder(insert_bst(t, x)) =~= inorder(*t.left) + seq![t.value] + inorder(insert_bst(*t.right, x))
{
    open bst(t);
    match t {
        Tree::Node(_, left, right) => {
            inorder_insert_increases_right(*right, x);
            assert(inorder(t) =~= inorder(*left) + seq![t.value] + inorder(*right));
        }
        Tree::Empty => {}
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
    if t0 is Empty {
        Tree::Node(x, Box::new(Empty), Box::new(Empty))
    } else {
        let n = t0.value;
        if x < n {
            let left = *t0.left;
            let new_left = insert_bst(left, x);
            Tree::Node(n, Box::new(new_left), t0.right)
        } else if n < x {
            let right = *t0.right;
            let new_right = insert_bst(right, x);
            Tree::Node(n, t0.left, Box::new(new_right))
        } else {
            t0
        }
    }
}
// </vc-code>

fn main() {}

}