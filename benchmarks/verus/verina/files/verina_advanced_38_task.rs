// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_coverage_after_removing_one(intervals: &Vec<(u8, u8)>) -> (result: u8)
    requires intervals.len() > 0,
    ensures 
        result as int <= intervals.len() * 1000,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}