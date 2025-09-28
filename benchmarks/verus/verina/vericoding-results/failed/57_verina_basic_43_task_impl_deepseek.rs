// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert spec functions to executable integer operations and remove nat cast issues */
fn sum_of_natural_numbers_exec(n: u64) -> u64 {
    n * (n + 1) / 2
}

fn sum_of_squares_of_natural_numbers_exec(n: u64) -> u64 {
    n * (n + 1) * (2 * n + 1) / 6
}

fn sum_of_cubes_of_natural_numbers_exec(n: u64) -> u64 {
    let sum_n = sum_of_natural_numbers_exec(n);
    sum_n * sum_n
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use u64 instead of int/nat to avoid ghost type compilation errors */
{
    let n_uint = n as u64;
    let s1 = sum_of_squares_of_natural_numbers_exec(n_uint) * 2;
    let s2 = sum_of_cubes_of_natural_numbers_exec(n_uint) * 4;
    let s3 = sum_of_natural_numbers_exec(n_uint) * 6;
    let result_uint = s1 - s2 + s3;
    proof {
        // Verify the result matches the expected formula
        assert(15 * (result_uint as nat) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n));
    }
    result_uint as nat
}
// </vc-code>

}
fn main() {}