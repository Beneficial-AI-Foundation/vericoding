// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn is_optimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==> (
        savings >= 0 &&
        (2 + savings) * (savings + 1) / 2 > n + 1 &&
        (savings == 0 || (2 + (savings - 1)) * savings / 2 <= n + 1)
    )
}

spec fn is_minimal_savings(n: int, savings: int) -> bool {
    n >= 1 ==> (
        is_optimal_savings(n, savings) &&
        (forall|j: int| j >= 0 && j < savings ==> #[trigger] ((2 + j) * (j + 1) / 2) <= n + 1)
    )
}

spec fn optimal_cost(n: int, savings: int) -> int {
    if n >= 1 && is_optimal_savings(n, savings) {
        n - savings + 1
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added trigger annotation to quantifier in invariant */
fn compute_minimal_savings(n: i64) -> (savings: i64)
    requires n >= 1
    ensures is_minimal_savings(n as int, savings as int)
{
    let mut s = 0;
    while (s+1)*(s+2)/2 <= n+1
        invariant
            s >= 0,
            forall|i: int| 0 <= i < s ==> (#[trigger] (i+1)*(i+2)/2) <= (n+1) as int,
        decreases (n+1) - (s+1)*(s+2)/2
    {
        s = s + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result as int >= 1,
        result as int <= n as int,
        exists|savings: int| is_minimal_savings(n as int, savings) && result as int == optimal_cost(n as int, savings),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed */
{
    let n_i64 = n as i64;
    let savings_i64 = compute_minimal_savings(n_i64);
    let result_i64 = n_i64 - savings_i64 + 1;
    result_i64 as i8
}
// </vc-code>


}

fn main() {}