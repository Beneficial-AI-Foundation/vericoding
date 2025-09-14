// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_product_even(arr: &Vec<u32>) -> (result: bool)

    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> !is_even(#[trigger] arr[k]),
        decreases arr.len() - i,
    {
        if arr[i] % 2 == 0 {
            assert(is_even(arr[i as int]));
            return true;
        }
        i += 1;
    }
    assert(forall|k: int| 0 <= k < arr.len() ==> !is_even(#[trigger] arr[k]));
    false
}
// </vc-code>

}
fn main() {}