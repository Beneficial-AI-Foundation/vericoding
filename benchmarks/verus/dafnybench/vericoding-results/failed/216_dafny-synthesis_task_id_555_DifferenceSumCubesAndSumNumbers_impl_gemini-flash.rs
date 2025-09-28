use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    // The given post-condition is `diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2`.
    // This simplifies to `diff == (n * (n + 1) / 2) * (n * (n + 1) / 2) - (n * (n + 1) / 2)`.
    // Let `s = n * (n + 1) / 2`. Then `diff == s * s - s`.
    // This `s` is the sum of numbers from 1 to `n`.
    // The sum of cubes from 1 to `n` is `(n * (n + 1) / 2)^2`.
    // So the post-condition simplifies to `diff == sum_cubes(n) - sum_numbers(n)`.
    // This function calculates the difference between the sum of cubes and the sum of numbers up to n.

    let sum_of_n_terms: u64 = (n as u64) * ((n as u64) + 1) / 2;
    let sum_of_n_cubes: u64 = sum_of_n_terms * sum_of_n_terms;

    let result_diff: u64 = sum_of_n_cubes - sum_of_n_terms;

    // The `ensures` clause directly states the mathematical formula.
    // We compute this formula using `u64` to avoid intermediate overflows if `n * (n+1)` is larger than `u32::MAX`.
    // Then we cast the final `u64` result to `u32`. This cast is safe if the result indeed fits `u32`.
    // Verus will check if `result_diff` can be safely cast to `u32`.
    // The `ensures` clause `diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2`
    // will be verified by the SMT solver, which confirms `result_diff as u32` equals the expected value.

    result_diff as u32
}
// </vc-code>

fn main() {}

}