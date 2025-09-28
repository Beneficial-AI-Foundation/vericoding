// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_index_property<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len()
    ensures s[i] == s[i]
{
    /* helper modified by LLM (iteration 2): removed problematic usize conversion */
}
// </vc-helpers>

// <vc-spec>
fn kth_element_impl(arr: &Vec<i32>, k: usize) -> (result: i32)
    requires k >= 1 && k <= arr.len(),
    ensures result == arr[k as int - 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): simplified proof to avoid type conversion */
    arr[k - 1]
}
// </vc-code>

}
fn main() {}