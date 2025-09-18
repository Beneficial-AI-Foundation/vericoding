// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using exec indexing arr[k-1] instead of spec arr@[k-1] */
    return arr[(k - 1)];
}
// </vc-code>

}
fn main() {}