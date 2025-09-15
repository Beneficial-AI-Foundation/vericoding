// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to match implementation approach */
spec fn sum_fourth_power_formula(n: nat) -> int {
    (n as int) * (2 * (n as int) + 1) * (7 + 24 * ((n as int) * (n as int) * (n as int)) - 12 * ((n as int) * (n as int)) - 14 * (n as int)) / 15
}

proof fn sum_fourth_power_lemma(n: nat)
    ensures sum_fourth_power_formula(n) * 15 == (n as int) * (2 * (n as int) + 1) * (7 + 24 * ((n as int) * (n as int) * (n as int)) - 12 * ((n as int) * (n as int)) - 14 * (n as int))
{
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost variable for nat return and proper casting */
    let mut sum: usize = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= n,
            15 * (sum as int) == (i as int) * (2 * (i as int) + 1) * (7 + 24 * ((i as int) * (i as int) * (i as int)) - 12 * ((i as int) * (i as int)) - 14 * (i as int))
    {
        let odd_num = 2 * i + 1;
        sum = sum + odd_num * odd_num * odd_num * odd_num;
        i = i + 1;
    }
    
    ghost let result_nat = sum as nat;
    result_nat
}
// </vc-code>

}
fn main() {}