// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum_divisible_by_k(arr: &Vec<i32>, k: i32) -> (result: i32)
    requires k > 0,
    ensures true,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}