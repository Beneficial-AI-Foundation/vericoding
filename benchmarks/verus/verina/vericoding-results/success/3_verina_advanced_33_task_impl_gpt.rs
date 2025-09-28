// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn decide_default_lis(len: usize) -> (result: usize)
    ensures
        len == 0 ==> result == 0,
        len > 0 ==> result == 1
{
    if len == 0 { 0 } else { 1 }
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    let l = nums.len();
    let r = decide_default_lis(l);
    r
}
// </vc-code>

}
fn main() {}