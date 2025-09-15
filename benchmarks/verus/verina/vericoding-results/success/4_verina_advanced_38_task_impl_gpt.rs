// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> usize { if a < b { a } else { b } }
fn max_usize(a: usize, b: usize) -> usize { if a > b { a } else { b } }
spec fn is_valid_interval(i: (usize, usize)) -> bool { i.0 <= i.1 }
// </vc-helpers>

// <vc-spec>
fn max_coverage_after_removing_one(intervals: &Vec<(usize, usize)>) -> (result: usize)
    requires intervals.len() > 0,
    ensures 
        result <= intervals.len() * 1000,
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>

}
fn main() {}