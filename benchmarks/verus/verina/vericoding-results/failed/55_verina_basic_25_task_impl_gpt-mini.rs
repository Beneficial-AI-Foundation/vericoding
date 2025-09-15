// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide sum formula helpers to compute triangular number safely */
fn sum_formula_u128(n: u32) -> u128 { (n as u128 * ((n as u128) + 1)) / 2 }
fn sum_formula_u32(n: u32) -> u32 { (n * (n + 1)) / 2 }
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute sum and average using integer arithmetic and convert for return */
    let s: u128 = sum_formula_u128(n);
    let sum_u32: u32 = s as u32;
    let avg: f64 = if n == 0 { 0.0 } else { (s as f64) / (n as f64) };
    (sum_u32, avg)
}
// </vc-code>

}
fn main() {}