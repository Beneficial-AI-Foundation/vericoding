use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn sum_cubes_formula(n: u32) -> u32
    ensures result == (n * n * (n + 1) * (n + 1)) / 4
{
    let mut sum = 0;
    let mut i = 1;
    while i <= n
        invariant
            i <= n + 1,
            sum == ((i - 1) * (i - 1) * i * i) / 4
    {
        sum = sum + (i * i * i);
        i = i + 1;
    }
    sum
}

proof fn sum_numbers_formula(n: u32) -> u32
    ensures result == (n * (n + 1)) / 2
{
    let mut sum = 0;
    let mut i = 1;
    while i <= n
        invariant
            i <= n + 1,
            sum == ((i - 1) * i) / 2
    {
        sum = sum + i;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    let sum_cubes = ((n as u64) * (n as u64) * ((n as u64) + 1) * ((n as u64) + 1)) / 4;
    let sum_nums = ((n as u64) * ((n as u64) + 1)) / 2;
    (sum_cubes - sum_nums) as u32
}
// </vc-code>

fn main() {}

}