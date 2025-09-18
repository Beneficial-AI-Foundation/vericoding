// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): convert 1-based k to 0-based index */
fn one_to_zero(k: usize) -> (result: usize)
    requires k >= 1,
    ensures result == k - 1,
{
    k - 1
}
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute 0-based index and return element */
    let idx: usize = one_to_zero(k);
    let result: i32 = arr[idx];
    result
}
// </vc-code>

}
fn main() {}