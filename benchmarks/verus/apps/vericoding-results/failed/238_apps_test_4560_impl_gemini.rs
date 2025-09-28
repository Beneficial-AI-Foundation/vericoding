// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 10000 && 0 <= a <= 1000
}

spec fn can_pay_exactly(n: int, a: int) -> bool {
    n % 500 <= a
}

spec fn valid_output(result: String) -> bool {
    result@ == "Yes"@ || result@ == "No"@
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect lemma name */
proof fn lemma_spec_impl_equivalence(n: i8, a: i8)
    requires valid_input(n as int, a as int),
    ensures can_pay_exactly(n as int, a as int) <==> ((n as i32) % 500 <= (a as i32)),
{
    let n_int = n as int;
    let a_int = a as int;

    // With `valid_input` and `n: i8`, we have `1 <= n_int <= 127`.
    // Thus, `n_int % 500` simplifies to `n_int`.
    // The spec condition `can_pay_exactly` simplifies to `n_int <= a_int`.
    vstd::arithmetic::div_mod::lemma_mod_of_nonneg(n_int, 500);

    // For machine integers, `1 <= (n as i32) <= 127`, so `(n as i32) % 500` is `(n as i32)`.
    // The implementation condition simplifies to `(n as i32) <= (a as i32)`.
    assert((n as i32) % 500 == (n as i32)) by(bit_vector);

    // For the relevant range, `int` and `i32` comparisons are equivalent.
    assert((n_int <= a_int) <==> ((n as i32) <= (a as i32))) by(bit_vector);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8) -> (result: String)
    requires 
        valid_input(n as int, a as int)
    ensures 
        valid_output(result) &&
        ((result@ == "Yes"@) <==> can_pay_exactly(n as int, a as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed, fix was in helper */
    lemma_spec_impl_equivalence(n, a);

    let n_val = n as i32;
    let a_val = a as i32;
    let result_str = if n_val % 500 <= a_val {
        String::from_str("Yes")
    } else {
        String::from_str("No")
    };
    result_str
}
// </vc-code>


}

fn main() {}