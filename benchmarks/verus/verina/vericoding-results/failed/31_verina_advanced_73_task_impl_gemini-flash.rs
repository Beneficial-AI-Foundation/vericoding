// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected type annotation for `l` in spec definition to reference `Seq<nat>`. */
fn smallest_missing_helper(l: Seq<nat>, low: nat, high: nat) -> (result: nat)
    requires
        low <= high,
        high <= l.len(),
        forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j]
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate),
{
    if low == high {
        low
    } else {
        let mid = low + (high - low) / 2;
        if l.len() <= mid || (l[mid] > mid) {
            smallest_missing_helper(l, low, mid)
        } else {
            smallest_missing_helper(l, mid + 1, high)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_missing(l: Seq<nat>) -> (result: nat)
    requires forall|i: int, j: int| 0 <= i < j < l.len() ==> l[i] < l[j],
    ensures
        !l.contains(result),
        forall|candidate: nat| candidate < result ==> l.contains(candidate)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error by removing the redundant `nat` type annotation. */
{
    if l.len() == 0 {
        0
    } else {
        smallest_missing_helper(l, 0, l.len())
    }
}
// </vc-code>

}
fn main() {}