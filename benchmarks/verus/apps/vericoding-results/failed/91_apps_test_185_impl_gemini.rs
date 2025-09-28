// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    2 <= n <= 5000 && 1 <= k <= n
}

spec fn optimal_moves(n: int, k: int) -> int {
    if k == 1 || k == n {
        3 * n
    } else {
        3 * n + spec_min(k - 1, n - k)
    }
}

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Retained correct helper from previous turn. */
fn min(a: i8, b: i8) -> (result: i8)
    ensures
        result as int == spec_min(a as int, b as int),
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn minimum_moves(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == optimal_moves(n as int, k as int),
        result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use 'int' for arithmetic to prevent i8 overflow */
    if k == 1 || k == n {
        (3 * (n as int)) as i8
    } else {
        let dist1 = k - 1;
        let dist2 = n - k;
        let min_dist = min(dist1, dist2);
        (3 * (n as int) + (min_dist as int)) as i8
    }
}
// </vc-code>


}

fn main() {}