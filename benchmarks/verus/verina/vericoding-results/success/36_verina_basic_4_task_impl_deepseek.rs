// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper function since direct access is sufficient */
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Direct array access with proper bounds */
{
    arr[k - 1]
}
// </vc-code>

}
fn main() {}