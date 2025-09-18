// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches by adding explicit nat conversions and base case handling */
spec fn fourth_power(x: nat) -> nat
{
    x * x * x * x
}

spec fn sum_fourth_power_helper(k: nat) -> nat
{
    if k == 0 {
        0
    } else {
        sum_fourth_power_helper((k - 1) as nat) + fourth_power((2 * k - 1) as nat)
    }
}

proof fn sum_fourth_power_formula(n: nat)
    ensures
        15 * sum_fourth_power_helper(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
    if n == 0 {
        assert(sum_fourth_power_helper(0) == 0);
        assert(15 * 0 == 0 * (2 * 0 + 1) * (7 + 24 * (0 * 0 * 0) - 12 * (0 * 0) - 14 * 0));
    } else {
        sum_fourth_power_formula((n - 1) as nat);
        let prev_sum = sum_fourth_power_helper((n - 1) as nat);
        let curr_term = fourth_power((2 * n - 1) as nat);
        assert(sum_fourth_power_helper(n) == prev_sum + curr_term);
        assert(curr_term == (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed nat literal syntax */
    let mut result: nat = 0;
    let mut i: nat = 1;
    let mut count: nat = 0;
    
    while count < n
        invariant
            count <= n,
            i == 2 * count + 1,
            result == sum_fourth_power_helper(count)
        decreases n - count
    {
        let fourth = i * i * i * i;
        result = result + fourth;
        i = i + 2;
        count = count + 1;
    }
    
    proof {
        sum_fourth_power_formula(n);
        assert(result == sum_fourth_power_helper(n));
    }
    
    result
}
// </vc-code>

}
fn main() {}