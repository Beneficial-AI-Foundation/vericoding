// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed to use int type to prevent potential overflow in multiplication */
    let num = n as int;
    let two_n = 2 * num;
    let term1 = two_n - 1;
    let term2 = two_n + 1;
    let sum_formula = (num * term1 * term2) / 3;
    sum_formula as u32
}
// </vc-code>

}
fn main() {}