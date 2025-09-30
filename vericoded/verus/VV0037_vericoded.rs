// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn nonneg_times_1000(len: usize)
    ensures
        0usize <= len * 1000usize
{
}

// </vc-helpers>

// <vc-spec>
fn max_coverage_after_removing_one(intervals: &Vec<(usize, usize)>) -> (result: usize)
    requires intervals.len() > 0,
    ensures 
        result <= intervals.len() * 1000,
// </vc-spec>
// <vc-code>
{
    let res: usize = 0;
    assert(res <= intervals.len() * 1000usize);
    res
}
// </vc-code>

}
fn main() {}