// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed requires/ensures from spec fn, as it's not allowed. */
spec fn kth_element_impl_spec(arr: &Vec<i32>, k: usize) -> (result: i32)
{
    arr[k as int - 1]
}
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Uses array indexing and `kth_element_impl_spec` */
{
    // Since the main function ensures the preconditions, we can directly access the element.
    // The `kth_element_impl_spec` can be used in ensures clauses but not directly called in executable code.
    // The `ensures` clause of `kth_element_impl` will ensure correctness.
    arr[k - 1]
}
// </vc-code>

}
fn main() {}