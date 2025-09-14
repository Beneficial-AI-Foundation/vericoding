// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes, a callable exec version of the spec function is needed */
fn is_even_exec(n: u32) -> (result: bool)
    ensures result == is_even(n)
{
    (n % 2) == 0
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(arr: &Vec<u32>) -> (result: bool)

    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix termination error */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(#[trigger] arr[k as int]),
        decreases arr.len() - i,
    {
        if is_even_exec(arr[i]) {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}