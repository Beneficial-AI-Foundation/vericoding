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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}