// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed compilation errors by using correct vstd paths and lemma names */
proof fn lemma_degrees_to_radians_properties(degrees: i64)
    ensures
        i64::MIN <= ((degrees as int * pi_approx()) / scale_factor()) / 180 <= i64::MAX,
{
    let d = degrees as int;
    let p = pi_approx();
    let s = scale_factor();
    let c = 180;

    let intermediate_res = (d * p) / s;

    // Prove that the expression is monotonic w.r.t. `d` because p, s, c are positive.
    // Therefore, the result for `d` is bounded by the results for i64::MIN and i64::MAX.
    vstd::arithmetic::mul::lemma_mul_le_mul_for_nonneg(i64::MIN as int, d, p);
    vstd::arithmetic::div_mod::lemma_div_is_monotonic((i64::MIN as int) * p, d * p, s);
    vstd::arithmetic::div_mod::lemma_div_is_monotonic(((i64::MIN as int) * p) / s, intermediate_res, c);

    vstd::arithmetic::mul::lemma_mul_le_mul_for_nonneg(d, i64::MAX as int, p);
    vstd::arithmetic::div_mod::lemma_div_is_monotonic(d * p, (i64::MAX as int) * p, s);
    vstd::arithmetic::div_mod::lemma_div_is_monotonic(intermediate_res, ((i64::MAX as int) * p) / s, c);
    
    // Now that the bounds are established, check that the extreme values are within i64 range.
    assert(i64::MIN <= (((i64::MIN as int * p) / s) / c)) by(compute);
    assert((((i64::MAX as int * p) / s) / c) <= i64::MAX) by(compute);
}
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation error; used vstd::integer not vstd::integers */
{
    proof {
        lemma_degrees_to_radians_properties(degrees);
    }

    let degrees_128 = degrees as i128;
    let pi_128 = pi_approx() as i128;
    let scale_128 = scale_factor() as i128;

    // This function correctly implements `(a * b) / d` for i128s, handling intermediate overflow.
    let intermediate_radians = vstd::integer::int_i128::i128_mul_div_to_i128(
        degrees_128,
        pi_128,
        scale_128,
    );

    let final_radians = intermediate_radians / 180;
    
    final_radians as i64
}
// </vc-code>

}
fn main() {}