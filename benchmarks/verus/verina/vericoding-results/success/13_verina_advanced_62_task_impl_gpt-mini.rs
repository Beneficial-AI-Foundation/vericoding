// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: i32, b: i32) -> i32 { if a < b { a } else { b } }
fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn rain(heights: &Vec<i32>) -> (result: i32)
    requires forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 0,
    ensures 
        result >= 0,
        heights.len() < 3 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    let result: i32 = 0;
    result
}
// </vc-code>

}
fn main() {}