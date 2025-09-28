// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): binary search for first missing value with int indices */
spec fn find_first_mismatch(l: Seq<nat>, lo: int, hi: int) -> (r: int)
    requires
        0 <= lo,
        lo <= hi,
        hi <= l.len() as int,
    ensures
        r >= 0,
        r <= l.len() as int,
        !l.contains(r as nat),
        forall|candidate: int| 0 <= candidate < r ==> l.contains(candidate as nat),
    decreases (hi - lo) as nat
{
    if lo < hi {
        let mid: int = (lo + hi) / 2;
        if l[mid] == mid as nat {
            find_first_mismatch(l, mid + 1, hi)
        } else {
            find_first_mismatch(l, lo, mid)
        }
    } else {
        lo
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
{
    /* code modified by LLM (iteration 5): call helper with int bounds and return nat result */
    let r_int = find_first_mismatch(l, 0, l.len() as int);
    r_int as nat
}
// </vc-code>

}
fn main() {}