use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: i32) -> (sum: i32)
    requires n > 0,
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15,
// </vc-spec>
// <vc-code>
{
    let nn: int = n as int;
    let a: int = 2 * nn + 1;
    let b: int = 24 * nn * nn * nn - 12 * nn * nn - 14 * nn + 7;
    let sum_int: int = nn * a * b / 15;
    sum_int as i32
}
// </vc-code>

fn main() {}

}