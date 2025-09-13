// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn is_optimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==>
    (savings >= 0 &&
     (2 + savings) * (savings + 1) / 2 > n + 1 &&
     (savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1))
}

spec fn is_minimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==>
    (is_optimal_savings(n, savings) &&
     (forall|j: int| j >= 0 && j < savings ==> (2 + j) * (j + 1) / 2 <= n + 1))
}

spec fn optimal_cost(n: int, savings: int) -> int {
    if n >= 1 && is_optimal_savings(n, savings) {
        n - savings + 1
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
    requires valid_input(n)
    ensures 
        result >= 1 &&
        result <= n &&
        exists|savings: int| is_minimal_savings(n, savings) && result == optimal_cost(n, savings)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}