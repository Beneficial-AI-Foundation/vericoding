// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_at(arr: &Vec<i32>, i: int) -> i32 { arr@[i] }
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    let idx: usize = k - 1;
    let result: i32 = arr[idx];
    result
}
// </vc-code>

}
fn main() {}