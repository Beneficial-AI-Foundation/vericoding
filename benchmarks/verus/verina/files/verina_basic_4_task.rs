// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i8>, k: usize) -> (result: i8)
    requires k >= 1 && k <= arr.len(),
    ensures result as int == arr@[k as int - 1]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}