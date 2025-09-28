// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed borrowing issue by using direct swapping */
spec fn is_sorted_two_way(s: Seq<bool>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> !s[i] || s[j]
}

proof fn multiset_swap_lemma<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed borrowing by reading values before mutations */
    let mut left = 0;
    let mut right = a.len();
    
    while left < right
        invariant
            0 <= left <= right <= a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> !a@[i],
            forall|i: int| right <= i < a.len() ==> a@[i],
        decreases
            right - left,
    {
        if !a[left] {
            left = left + 1;
        } else if a[right - 1] {
            right = right - 1;
        } else {
            proof {
                multiset_swap_lemma(a@, left as int, (right - 1) as int);
            }
            let left_val = a[left];
            let right_val = a[right - 1];
            a.set(left, right_val);
            a.set(right - 1, left_val);
            left = left + 1;
            right = right - 1;
        }
    }
}
// </vc-code>

}
fn main() {}