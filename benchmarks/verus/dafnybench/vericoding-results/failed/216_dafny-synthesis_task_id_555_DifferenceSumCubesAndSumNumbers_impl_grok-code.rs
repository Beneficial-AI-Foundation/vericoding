use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn difference_sum_cubes_and_sum_numbers(n: u32) -> (diff: u32)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
// </vc-spec>
// <vc-code>
{
    let sum_of_cubes_int: Ghost<int> = Ghost(0);
    let sum_of_numbers_int: Ghost<int> = Ghost(0);
    proof {
        sum_of_cubes_int@ = (n as int * n as int * (n as int + 1) * (n as int + 1)) / 4;
        sum_of_numbers_int@ = (n as int * (n as int + 1)) / 2;
    }
    let diff_int = sum_of_cubes_int@ - sum_of_numbers_int@;
    assert(diff_int >= 0 && diff_int <= 0xffff_ffffu32 as int);
    diff_int as u32
}
// </vc-code>

fn main() {}

}