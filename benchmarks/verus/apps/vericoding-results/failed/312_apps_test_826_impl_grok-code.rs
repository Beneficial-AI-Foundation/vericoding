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
exec fn find_minimal_savings(nn: usize) -> (r: usize)
    requires nn >= 1
    ensures is_minimal_savings(nn as int, r as int)
{
    /* helper modified by LLM (iteration 4): fixed infinite loop warning to use loop and added trigger to quantifier */
    let mut savings: usize = 0;
    loop
        invariant
            forall|j: int| j >= 0 && j < savings as int ==> #[trigger] ((2 + j) * (j + 1) / 2) <= nn as int + 1,
            (savings == 0 || (2 + (savings as int - 1)) * (savings as int) / 2 <= nn as int + 1),
            savings as int <= nn as int + 2
        decreases (nn as int + 2) - (savings as int)
    {
        let current: usize = (2 + savings) * (savings + 1) / 2;
        if current > nn + 1 {
            break;
        }
        savings = savings + 1;
    }
    savings
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
/* code modified by LLM (iteration 4): ensured type safety and assertions for correct result */
{
    let nn_usize = n as usize;
    let savings = find_minimal_savings(nn_usize);
    proof {
        let savings_int = savings as int;
        assert(is_minimal_savings(n as int, savings_int));
        assert((n as int - savings_int + 1) == optimal_cost(n as int, savings_int));
    }
    let result: i8 = (n as i32 - savings as i32 + 1) as i8;
    result
}
// </vc-code>


}

fn main() {}