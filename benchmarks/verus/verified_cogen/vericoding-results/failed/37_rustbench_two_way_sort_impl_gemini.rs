// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no new helpers needed */
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
/* code modified by LLM (iteration 5): fixed path to lemma_swap_preserves_multiset */
{
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut low: usize = 0;
    let mut high: usize = n - 1;

    while low < high
        invariant
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            0 <= low,
            high < a.len(),
            low <= high + 1,
            forall|i: int| 0 <= i < low ==> !a[i],
            forall|i: int| high < i < a.len() ==> a[i],
        decreases high - low,
    {
        if !a[low] {
            low = low + 1;
        } else if a[high] {
            high = high - 1;
        } else {
            // a[low] is true and a[high] is false, swap them
            proof {
                vstd::seq::lemma_swap_preserves_multiset(a@, low as int, high as int);
            }
            let temp = a[low];
            a.set(low, a[high]);
            a.set(high, temp);

            low = low + 1;
            if high > 0 {
                high = high - 1;
            }
        }
    }
}
// </vc-code>

}
fn main() {}