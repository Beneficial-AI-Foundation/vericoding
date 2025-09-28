// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed result scope error by returning sum directly */
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n
        invariant
            sum as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3,
        decreases n - i
    {
        sum = sum + (2 * i + 1) * (2 * i + 1);
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}