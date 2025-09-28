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
proof fn lemma_optimal_savings_upper_bound(n: int, savings: int)
    requires
        n >= 1,
    ensures
        (2 + savings) * (savings + 1) / 2 > n + 1 ==> savings >= 0 && (forall|j: int| j >= 0 && j < savings ==> #[trigger] ((2 + j) * (j + 1) / 2) <= n + 1)
{
    if (2 + savings) * (savings + 1) / 2 > n + 1 {
        assert(savings >= 0);
        let mut j: int = 0;
        while j < savings
            invariant
                j >= 0,
                forall|k: int| k >= 0 && k < j ==> #[trigger] ((2 + k) * (k + 1) / 2) <= n + 1,
            decreases savings - j
        {
            assert((2 + j) * (j + 1) / 2 <= (2 + (savings - 1)) * savings / 2);
            assert((2 + j) * (j + 1) / 2 <= n + 1);
            j = j + 1;
        }
    }
}

proof fn lemma_minimal_savings_exists(n: int)
    requires
        n >= 1,
    ensures
        exists|s: int| is_minimal_savings(n, s)
{
    let mut s = 0;
    while (2 + s) * (s + 1) / 2 <= n + 1
        invariant
            s >= 0,
            forall|k: int| k >= 0 && k < s ==> #[trigger] ((2 + k) * (k + 1) / 2) <= n + 1,
        decreases n + 2 - s
    {
        s = s + 1;
    }
    lemma_optimal_savings_upper_bound(n, s);
    assert(is_minimal_savings(n, s));
    assert(optimal_cost(n, s) == n - s + 1);
}

proof fn lemma_solution_range(n: int, savings: int)
    requires
        n >= 1,
        is_minimal_savings(n, savings),
    ensures
        optimal_cost(n, savings) >= 1,
        optimal_cost(n, savings) <= n
{
    assert(savings >= 0);
    assert((2 + savings) * (savings + 1) / 2 > n + 1);
    let cost = optimal_cost(n, savings);
    assert(cost == n - savings + 1);
    assert(cost >= 1);
    assert(cost <= n);
}
proof fn lemma_optimal_savings_cast(n: i8, savings: i8)
    requires
        n >= 1;
        savings >= 0,
    ensures
        (2 + savings as int) * (savings as int + 1) / 2 <= n as int + 1 <==> (2 + (savings as int)) * ((savings as int) + 1) / 2 <= n as int + 1
{
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
    /* code modified by LLM (iteration 5): fixed type casting in while condition */
    assert(n >= 1);
    let mut savings: i8 = 0;
    while {
        let s = savings as int;
        (2 + s) * (s + 1) / 2 <= n as int + 1
    }
        invariant
            savings >= 0,
            (2 + (savings as int - 1)) * (savings as int) / 2 <= n as int + 1,
        decreases (n as int + 2 - savings as int)
    {
        savings = savings + 1;
    }
    let result = n - savings + 1;
    proof {
        lemma_optimal_savings_upper_bound(n as int, savings as int);
        lemma_solution_range(n as int, savings as int);
        assert(optimal_cost(n as int, savings as int) == result as int);
    }
    result
}
// </vc-code>


}

fn main() {}