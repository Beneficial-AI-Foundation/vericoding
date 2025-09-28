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
/* helper modified by LLM (iteration 5): Fixed int type usage in exec code by using ghost variables */
proof fn lemma_arithmetic_sum(k: int)
    requires k >= 0
    ensures (2 + k) * (k + 1) / 2 == k + 1 + k * (k + 1) / 2
{
}

proof fn lemma_sum_monotonic(k1: int, k2: int)
    requires k1 >= 0, k2 >= k1
    ensures (2 + k1) * (k1 + 1) / 2 <= (2 + k2) * (k2 + 1) / 2
{
}

proof fn lemma_savings_bounds(n: int, savings: int)
    requires n >= 1, is_optimal_savings(n, savings)
    ensures savings >= 0, savings <= n
{
}

proof fn lemma_optimal_unique(n: int, s1: int, s2: int)
    requires n >= 1, is_optimal_savings(n, s1), is_optimal_savings(n, s2)
    ensures s1 == s2
{
}

fn find_savings(n: i8) -> (savings: i8)
    requires valid_input(n as int)
    ensures 
        savings >= 0,
        is_optimal_savings(n as int, savings as int),
        is_minimal_savings(n as int, savings as int)
{
    let mut s: i8 = 0;
    
    while s < n
        invariant
            s >= 0,
            s <= n,
            forall|j: int| j >= 0 && j < s ==> (2 + j) * (j + 1) / 2 <= (n as int) + 1
    {
        let ghost n_int: int = n as int;
        let ghost s_int: int = s as int;
        let ghost sum: int = (2 + s_int) * (s_int + 1) / 2;
        if sum > n_int + 1 {
            break;
        }
        s = s + 1;
    }
    
    proof {
        lemma_savings_bounds(n as int, s as int);
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
{
    /* code modified by LLM (iteration 5): Fixed int type usage in exec code by using ghost variables */
    let savings = find_savings(n);
    let result = n - savings + 1;
    
    proof {
        lemma_optimal_unique(n as int, savings as int, savings as int);
        assert(is_minimal_savings(n as int, savings as int));
        assert(result as int == optimal_cost(n as int, savings as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}