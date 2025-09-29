// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_usize_sub_lt_self(k: usize)
    requires
        k >= 1,
    ensures
        k - 1 < k
{
}

// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    let idx: usize = k - 1;
    assert(k >= 1 && k <= arr.len());
    assert(idx < k);
    assert(idx < arr.len());
    let v = arr[idx];
    assert(v == arr[k as int - 1]);
    v
}
// </vc-code>

}
fn main() {}