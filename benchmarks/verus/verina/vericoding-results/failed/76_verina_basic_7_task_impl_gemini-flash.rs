// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added `decreases` clause to the recursive `spec fn`. */
spec fn sum_of_squares_of_first_n_odd_numbers_spec(n: int) -> int
decreases n
{
    if n == 0 {
        0
    } else if n < 0 {
        0
    } else {
        let term = 2 * n - 1;
        sum_of_squares_of_first_n_odd_numbers_spec(n - 1) + term * term
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes were needed in this section as helper was fixed. */
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;

    while i < n as u64
        invariant 
            sum as int == sum_of_squares_of_first_n_odd_numbers_spec(i as int),
            i <= n as u64,
        decreases (n as u64 - i)
    {
        let odd_num = 2 * i + 1;
        sum = sum + odd_num * odd_num;
        i = i + 1;
    }
    
    sum as u32
}
// </vc-code>

}
fn main() {}