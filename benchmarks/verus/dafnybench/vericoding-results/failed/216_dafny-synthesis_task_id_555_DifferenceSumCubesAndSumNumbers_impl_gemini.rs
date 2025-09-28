// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_formula(n: int) -> int {
    (n * (n + 1)) / 2
}

fn sum_first_n_integers(n: u32) -> (sum: u64)
    ensures
        sum as int == sum_formula(n as int),
{
    (n as u64 * (n as u64 + 1)) / 2
}

fn sum_first_n_cubes(n: u32) -> (sum_cubes: u128)
    ensures
        sum_cubes as int == sum_formula(n as int) * sum_formula(n as int),
{
    let sum_n = sum_first_n_integers(n) as u128;
    sum_n * sum_n
}
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    let sum_of_cubes = sum_first_n_cubes(n);
    let sum_of_integers = sum_first_n_integers(n) as u128;
    (sum_of_cubes - sum_of_integers) as u32
}
// </vc-code>

}
fn main() {}