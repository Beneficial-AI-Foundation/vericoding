// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): corrected incorrect module path for arithmetic lemmas */
proof fn properties_of_mult_by_3(x: i32)
    ensures
        ((x as int) * 3) / 3 == (x as int),
        ((x as int) * 3) % 3 == 0,
{
    vstd::arithmetic::mul::lemma_mul_div_identity(x as int, 3);
    vstd::arithmetic::mul::lemma_mul_mod_noop(x as int, 3);
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
    /* code modified by LLM (iteration 5): added proof block and lemma call for second postcondition */
    let result = x * 3;
    proof {
        properties_of_mult_by_3(x);
        vstd::arithmetic::div_mod::lemma_div_multiplies_to_self(result as int, 3);
    }
    result
}
// </vc-code>

}
fn main() {}