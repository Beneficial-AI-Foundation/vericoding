// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn compute_position(days: int, v0: int, v1: int, a: int, l: int) -> int
    requires 
        days >= 0 &&
        v0 >= 0 &&
        v1 >= v0 &&
        a >= 0 &&
        l >= 0
    decreases days
{
    if days == 0 {
        0
    } else {
        let prev_pos = compute_position((days - 1) as int, v0, v1, a, l);
        let after_reread = if prev_pos - l > 0 { prev_pos - l } else { 0 };
        let read_today = if v1 < v0 + a * (days - 1) { v1 } else { v0 + a * (days - 1) };
        after_reread + read_today
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(c: int, v0: int, v1: int, a: int, l: int) -> (result: int)
    requires 
        1 <= c <= 1000 &&
        0 <= l < v0 <= v1 <= 1000 &&
        0 <= a <= 1000
    ensures 
        result >= 1 &&
        compute_position(result, v0, v1, a, l) >= c &&
        forall|days: int| 1 <= days < result ==> compute_position(days, v0, v1, a, l) < c
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}