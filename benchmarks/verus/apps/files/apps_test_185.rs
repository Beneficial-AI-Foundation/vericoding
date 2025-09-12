// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn minimum_moves(n: int, k: int) -> (result: int)
    requires 
        valid_input(n, k)
    ensures 
        result == optimal_moves(n, k),
        result > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}