// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn preserved(a_old: Seq<i32>, a_new: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a_old.len() && a_old.len() == a_new.len()
{
    a_old.subrange(left as int, right as int).to_multiset() == a_new.subrange(left as int, right as int).to_multiset()
}

spec fn ordered(a: Seq<i32>, left: nat, right: nat) -> bool
    recommends left <= right <= a.len()
{
    forall|i: int| #![trigger a[i]] left < i < right ==> a[i-1] <= a[i]
}

spec fn sorted(a_old: Seq<i32>, a_new: Seq<i32>) -> bool
    recommends a_old.len() == a_new.len()
{
    ordered(a_new, 0, a_new.len() as nat) && preserved(a_old, a_new, 0, a_old.len() as nat)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change, was correct */
fn find_min_index(a: &Vec<i32>, start: usize) -> (min_idx: usize)
    requires
        start < a.len(),
    ensures
        start <= min_idx < a.len(),
        forall|k: int| start as int <= k < a.len() as int ==> a@[min_idx as int] <= a@[k],
{
    let mut min_idx = start;
    let mut j = start + 1;
    while j < a.len()
        invariant
            start < a.len(),
            start <= min_idx < a.len(),
            start < j <= a.len(),
            forall|k: int| start as int <= k < j as int ==> a@[min_idx as int] <= a@[k],
        decreases a.len() - j
    {
        if a[j] < a[min_idx] {
            min_idx = j;
        }
        j = j + 1;
    }
    min_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures sorted(old(a)@, a@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): used Vec::swap and added a proof block to prove multiset preservation */
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            i <= a.len(),
            ordered(a@, 0, i as nat),
            forall |j: int, k: int| 0 <= j < i as int && i as int <= k < a.len() as int ==> a@[j] <= a@[k],
        decreases a.len() - i
    {
        if i + 1 < a.len() {
            let min_idx = find_min_index(a, i);

            proof {
                let pre_swap_a_seq = a@;
                a.swap(i, min_idx);
                vstd::seq_lib::lemma_swap_preserves_multiset(pre_swap_a_seq, i as int, min_idx as int);
            }
        } else {
            // No-op, invariants are maintained trivially
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}