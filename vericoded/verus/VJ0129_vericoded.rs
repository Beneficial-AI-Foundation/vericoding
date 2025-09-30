// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): exec mode helper for checking if number is even */
fn is_even_exec(n: u32) -> (result: bool)
    ensures
        result <==> is_even(n),
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
    /* code modified by LLM (iteration 2): use exec mode helper instead of spec function */
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k]),
    {
        if is_even_exec(arr[i])
        {
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}