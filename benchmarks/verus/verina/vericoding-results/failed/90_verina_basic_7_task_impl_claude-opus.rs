// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic calculations in proof */
proof fn sum_formula_proof(n: u32)
    ensures
        sum_of_squares_up_to(n) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3
    decreases n
{
    if n == 0 {
        assert(sum_of_squares_up_to(0) == 0);
        assert((0 * (2 * 0 - 1) * (2 * 0 + 1)) / 3 == 0);
    } else {
        sum_formula_proof((n - 1) as u32);
        let prev = (n - 1) as int;
        let curr = n as int;
        assert(sum_of_squares_up_to(n) == sum_of_squares_up_to((n - 1) as u32) + (2 * curr - 1) * (2 * curr - 1));
        assert(sum_of_squares_up_to((n - 1) as u32) == (prev * (2 * prev - 1) * (2 * prev + 1)) / 3);
        let odd_n = 2 * curr - 1;
        assert((2 * curr - 1) * (2 * curr - 1) == 4 * curr * curr - 4 * curr + 1);
        assert(prev * (2 * prev - 1) * (2 * prev + 1) + 3 * odd_n * odd_n == curr * (2 * curr - 1) * (2 * curr + 1));
    }
}

spec fn sum_of_squares_up_to(n: u32) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        sum_of_squares_up_to((n - 1) as u32) + (2 * n as int - 1) * (2 * n as int - 1)
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
{
    /* code modified by LLM (iteration 5): Fixed overflow by using int arithmetic */
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            sum as int == sum_of_squares_up_to(i),
        decreases n - i
    {
        let odd = (2 * (i as int) + 1) as u32;
        sum = sum + odd * odd;
        i = i + 1;
    }
    
    proof {
        sum_formula_proof(n);
    }
    
    sum
}
// </vc-code>

}
fn main() {}