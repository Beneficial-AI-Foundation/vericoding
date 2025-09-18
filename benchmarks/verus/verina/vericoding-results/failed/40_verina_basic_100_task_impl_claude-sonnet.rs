// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to check overflow bounds and divisibility properties */
fn can_triple_safely(x: i32) -> bool {
    x >= i32::MIN / 3 && x <= i32::MAX / 3
}

lemma lemma_triple_division(x: i32)
    requires can_triple_safely(x)
    ensures (x * 3) / 3 == x
    ensures (x * 3) / 3 * 3 == x * 3
{
    let product = x * 3;
    assert(product % 3 == 0);
    assert(product / 3 == x);
    assert(product / 3 * 3 == product);
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add precondition checking and use lemma for verification */
    assert(can_triple_safely(x));
    lemma_triple_division(x);
    let result = x * 3;
    result
}
// </vc-code>

}
fn main() {}