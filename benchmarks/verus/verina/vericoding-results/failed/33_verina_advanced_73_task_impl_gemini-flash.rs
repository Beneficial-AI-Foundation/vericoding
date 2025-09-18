// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty helper section */
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add explicit `ghost` keyword to `result` to allow `nat` type. Make sure array indexing uses `usize`. */
{
    let mut low: usize = 0;
    let mut high_usize: usize = l.len(); // Adjusted high_usize to be l.len() to match typical binary search on indices range [low, high)
    let mut ghost result: nat = l.len() as nat; // Renamed from result_ghost

    if l.len() == 0 {
        return 0;
    }

    while low < high_usize
        invariant
            0 <= low,
            low <= high_usize,
            high_usize <= l.len(),
            (result as int) <= l.len() as int,
            // Any element before 'low' (if present) is its index.
            // This invariant ensures that for all i in [0, low), l[i] == i
            forall|k: int| 0 <= k < low as int ==> l[k] == k as nat,
            // If l[i] > i, result is at most i.
            // This invariant means that for all i in [high_usize, l.len()), l[i] > i implies result <= i
            forall|k: int| high_usize as int <= k < l.len() as int ==> l[k] > k as nat ==> result <= k as nat,
            // All candidates smaller than current result have been found to be present.
            forall|candidate: nat| candidate < result ==> l.contains(candidate),
    {
        let mid: usize = low + (high_usize - low) / 2;
        // l[mid] is nat, mid is usize. Compare l[mid] (nat) with mid as nat.
        if l[mid] == mid as nat {
            // The current element is in place, so the smallest missing must be after mid
            low = mid + 1;
        } else {
            // The current element is greater than its index, so 'mid' might be the smallest missing number
            result = mid as nat;
            high_usize = mid;
        }
    }
    result
}
// </vc-code>

}
fn main() {}