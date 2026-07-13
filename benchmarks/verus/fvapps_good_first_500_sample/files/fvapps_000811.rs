// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_list(xs: Seq<u32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        xs[0] as int + sum_list(xs.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn find_max_segment_scores(n: u32, m: u32, arr: Seq<u32>) -> (result: (u32, u32))
    requires 
        n > 0,
        arr.len() == n,
        m > 0
    ensures
        result.0 < m,
        result.1 > 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0u32, 1u32)
    // impl-end
}
// </vc-code>


}
fn main() {}