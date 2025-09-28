// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

spec fn min_cost_to_divisible(n: int, m: int, a: int, b: int) -> int {
    let k = n % m;
    if k * b < (m - k) * a { k * b } else { (m - k) * a }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes were needed, kept existing spec function for clarity. */
spec fn result_fits_in_i8(n: int, m: int, a: int, b: int) -> bool {
    let cost = min_cost_to_divisible(n, m, a, b);
    0 <= cost && cost <= 127
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a as int, b as int)
    ensures 
        result as int == min_cost_to_divisible(n as int, m as int, a as int, b as int),
        result as int >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by removing incorrect proof syntax and using a direct assertion. */
    let n_i64 = n as i64;
    let m_i64 = m as i64;
    let a_i64 = a as i64;
    let b_i64 = b as i64;

    let k = n_i64 % m_i64;

    let cost_to_decrease = k * b_i64;
    let cost_to_increase = (m_i64 - k) * a_i64;

    let result_i64 = if cost_to_decrease < cost_to_increase {
        cost_to_decrease
    } else {
        cost_to_increase
    };

    proof {
        let n_int = n as int;
        let m_int = m as int;
        let a_int = a as int;
        let b_int = b as int;

        // Assert that the remainder calculated with i64 is equivalent to the spec's int version.
        // This holds because the original values are i8.
        assert(k as int == n_int % m_int);

        // With the above assertion, Verus can deduce that the rest of the calculation matches the spec function.
        assert(result_i64 as int == min_cost_to_divisible(n_int, m_int, a_int, b_int));
    }

    // The cast to i8 is unprovable with the given spec, as the result can exceed 127.
    // A counterexample is n=51, m=127, a=2, b=3, which gives result 152.
    // A precondition `requires result_fits_in_i8(n, m, a, b)` would be needed.
    result_i64 as i8
}
// </vc-code>


}

fn main() {}