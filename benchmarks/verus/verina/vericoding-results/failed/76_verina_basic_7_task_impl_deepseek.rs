// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sum_of_squares_formula(n: nat) 
    ensures 
        (sum_of_squares_of_first_n_odd_numbers(n as u32) as int == (n * (2 * n - 1) * (2 * n + 1)) / 3),
    decreases n,
{
    if n > 0 {
        lemma_sum_of_squares_formula((n - 1) as nat);
    }
}

fn sum_of_squares_of_first_n_odd_numbers_exec(n: u32) -> u32
    requires n >= 0,
    ensures
        result == sum_of_squares_of_first_n_odd_numbers(n),
{
    let mut sum: u32 = 0;
    let mut count: u32 = 0;
    let mut current_odd: u32 = 1;
    
    while count < n
        invariant
            count <= n,
            sum == sum_of_squares_of_first_n_odd_numbers(count),
            current_odd == 2 * count + 1,
        decreases n - count,
    {
        sum = sum + current_odd * current_odd;
        current_odd = current_odd + 2;
        count = count + 1;
    }
    sum
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
    /* code modified by LLM (iteration 5): Remove unnecessary variable declaration */
    sum_of_squares_of_first_n_odd_numbers_exec(n)
}
// </vc-code>

}
fn main() {}