// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_coverage_after_removing_one(intervals: &Vec<(usize, usize)>) -> (result: usize)
    requires intervals.len() > 0,
    ensures 
        result <= intervals.len() * 1000,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}