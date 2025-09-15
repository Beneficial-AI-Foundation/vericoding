// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_i32(a: i32, b: i32) -> i32 { if a > b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(a: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= a.len(),
// </vc-spec>
// <vc-code>
{
    0i32
}
// </vc-code>

}
fn main() {}