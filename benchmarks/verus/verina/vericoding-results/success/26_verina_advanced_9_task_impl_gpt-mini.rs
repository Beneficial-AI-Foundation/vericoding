// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove basic division bound */
proof fn div_le_n(n: usize, d: usize)
    requires d > 0,
    ensures n / d <= n
{
    assert(n / d <= n);
}

// </vc-helpers>

// <vc-spec>
fn count_sum_divisible_by(n: usize, d: usize) -> (result: usize)
    requires d > 0,
    ensures 
        result <= n,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute count as quotient n/d */
    let result: usize = n / d;
    result
}
// </vc-code>

}
fn main() {}