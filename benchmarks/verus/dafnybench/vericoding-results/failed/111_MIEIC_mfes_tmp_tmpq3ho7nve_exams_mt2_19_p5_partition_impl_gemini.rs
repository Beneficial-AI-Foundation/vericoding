// <vc-preamble>
use vstd::prelude::*;

verus! {

type T = int;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof for multiset preservation */
fn swap(a: &mut Vec<T>, i: usize, j: usize)
    requires
        0 <= i < old(a).len(),
        0 <= j < old(a).len(),
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        a@[i as int] == old(a)@[j as int],
        a@[j as int] == old(a)@[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a@[k] == old(a)@[k],
{
    let ghost old_a_seq = a@;
    let val_i = a[i];
    let val_j = a[j];
    a.set(i, val_j);
    a.set(j, val_i);
    proof {
        assert(a@ =~= old_a_seq.swap(i as int, j as int));
        vstd::seq_lib::lemma_swap_preserves_multiset(old_a_seq, i as int, j as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<T>) -> (pivotPos: usize)
    requires 
        old(a).len() > 0,
    ensures 
        pivotPos < a.len(),
        forall|i: int| 0 <= i < pivotPos ==> a[i] < a[pivotPos as int],
        forall|i: int| pivotPos < i < a.len() ==> a[i] >= a[pivotPos as int],
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): refactored to use a 'last' variable for clarity and fixed invariants */
    let ghost old_a_seq = a@;
    let n = a.len();
    let last = n - 1;

    let pivot_val = a[last];

    let mut i: usize = 0;
    let mut j: usize = 0;
    while j < last
        invariant
            n == a.len(),
            a@.to_multiset() == old_a_seq.to_multiset(),
            0 <= i <= j <= last,
            a[last] == pivot_val,
            forall|k: int| 0 <= k < i ==> a[k] < pivot_val,
            forall|k: int| i <= k < j ==> a[k] >= pivot_val,
        decreases last - j
    {
        if a[j] < pivot_val {
            swap(a, i, j);
            i = i + 1;
        }
        j = j + 1;
    }

    swap(a, i, last);

    i
}
// </vc-code>

}
fn main() {}