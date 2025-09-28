// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn sheets_needed(n: int) -> (int, int, int) {
    (2 * n, 5 * n, 8 * n)
}

spec fn total_sheets_needed(n: int) -> int {
    2 * n + 5 * n + 8 * n
}

spec fn ceil_div(a: int, b: int) -> int
    recommends b > 0
{
    (a + b - 1) / b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed integer type from i8 to int parameters */
proof fn lemma_ceil_div_positive(a: int, b: int)
    requires
        a >= 0,
        b > 0
    ensures
        (a + b - 1) / b >= 0
{
}

proof fn lemma_ceil_div_sum(a: int, b: int, c: int, d: int)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
        d > 0
    ensures
        (a + b + c + d - 1) / d <= (a + d - 1) / d + (b + d - 1) / d + (c + d - 1) / d
{
}

proof fn lemma_total_sheets_bounds(n: int, k: int)
    requires
        n >= 1,
        k > 0
    ensures
        (2 * n + k - 1) / k + (5 * n + k - 1) / k + (8 * n + k - 1) / k >= (15 * n + k - 1) / k
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == ceil_div(2 * (n as int), k as int) + ceil_div(5 * (n as int), k as int) + ceil_div(8 * (n as int), k as int),
        result >= 0,
        result as int >= (total_sheets_needed(n as int) + (k as int) - 1) / (k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed casts in helper calls and division operations */
    let n_int = n as int;
    let k_int = k as int;
    
    let sheets_2 = ((2 * n) + k - 1) / k;
    let sheets_5 = ((5 * n) + k - 1) / k;
    let sheets_8 = ((8 * n) + k - 1) / k;
    let total = sheets_2 + sheets_5 + sheets_8;
    
    proof {
        lemma_ceil_div_positive(2 * n_int, k_int);
        lemma_ceil_div_positive(5 * n_int, k_int);
        lemma_ceil_div_positive(8 * n_int, k_int);
        lemma_total_sheets_bounds(n_int, k_int);
    }
    assert(total >= 0) by (bit_vector);
    total
}
// </vc-code>


}

fn main() {}