// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

spec fn min(x: int, y: int) -> int {
    if x < y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x > y { x } else { y }
}

spec fn interval_overlap_length(a: int, b: int, c: int, d: int) -> int {
    if min(b, d) - max(a, c) > 0 { min(b, d) - max(a, c) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed to use i8 instead of int */
fn compute_overlap(a: i8, b: i8, c: i8, d: i8) -> (overlap: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        overlap as int == interval_overlap_length(a as int, b as int, c as int, d as int),
        overlap >= 0,
        overlap <= 100,
{
    let start = a.max(c);
    let end = b.min(d);
    if start < end {
        end - start
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        result >= 0,
        result as int == interval_overlap_length(a as int, b as int, c as int, d as int),
        result <= 100,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use i8 helper function */
{
    let overlap = compute_overlap(a, b, c, d);
    overlap
}
// </vc-code>


}

fn main() {}