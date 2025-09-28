// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_k(n: nat) -> nat
    ensures
        result == n * (n + 1) / 2
    decreases n
{
    if n == 0 { 0 } else { sum_k(n-1) + n }
}

spec fn sum_k_square(n: nat) -> nat
    ensures
        result == n * (n + 1) * (2 * n + 1) / 6
    decreases n
{
    if n == 0 { 0 } else { sum_k_square(n-1) + n * n }
}

spec fn sum_k_cube(n: nat) -> nat
    ensures
        result == (n * (n + 1) / 2) * (n * (n + 1) / 2)
    decreases n
{
    if n == 0 { 0 } else { sum_k_cube(n-1) + n * n * n }
}

spec fn sum_k_fourth(n: nat) -> nat
    ensures
        result == n * (n + 1) * (2 * n + 1) * (3 * n * n - 3 * n - 1) / 30
    decreases n
{
    if n == 0 { 0 } else { sum_k_fourth(n-1) + n * n * n * n }
}

spec fn sum_odd4(n: nat) -> nat
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n)
{
    16 * sum_k_fourth(n) - 32 * sum_k_cube(n) + 24 * sum_k_square(n) - 8 * sum_k(n) + n
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    sum_odd4(n)
}
// </vc-code>

}
fn main() {}