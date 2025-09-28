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
{
    /* code modified by LLM (iteration 5): Fixed while condition to use i8 operations instead of int */
    let mut savings: i8 = 0;
    let ghost mut sum: int = 0;
    let ghost n_int = n as int;
    
    // Use i8 arithmetic in the condition
    while savings <= 127 && (savings * (savings + 3)) / 2 <= n + 1
        invariant
            0 <= savings <= 127,
            sum == (2 + (savings as int) - 1) * (savings as int) / 2,
            forall|j: int| 0 <= j && j < savings as int ==> #[trigger] ((2 + j) * (j + 1) / 2) <= n_int + 1,
            savings as int * (savings as int + 3) / 2 <= n_int + 1 || (2 + savings as int) * (savings as int + 1) / 2 > n_int + 1,
        decreases
            n as int + 1 - savings as int,
    {
        savings = savings + 1;
        proof {
            sum = (2 + (savings as int) - 1) * (savings as int) / 2;
        }
    }
    
    proof {
        let s = savings as int;
        assert(sum == (2 + s - 1) * s / 2);
        assert((2 + s) * (s + 1) / 2 > n_int + 1);
        assert(s == 0 || (2 + (s - 1)) * s / 2 <= n_int + 1);
        assert(is_optimal_savings(n_int, s));
        assert(is_minimal_savings(n_int, s));
    }
    
    let result = n - savings + 1;
    result
}
// </vc-code>


}

fn main() {}