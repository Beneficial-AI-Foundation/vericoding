// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed type mismatch in ensures clause by converting index to int */
fn get_element(arr: &Vec<i32>, index: usize) -> (result: i32)
    requires index < arr.len(),
    ensures result == arr[index as int]
{
    arr[index]
}
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no changes needed, but added comment as per iteration 2 */
    let index = k - 1;
    get_element(arr, index)
}
// </vc-code>

}
fn main() {}