// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Lemma that for positive d, floor division n/d is bounded by n */
proof fn lemma_division_bound(n: usize, d: usize)
    requires d > 0
    ensures n / d <= n
{
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
    /* code modified by LLM (iteration 2): compute floor(n/d) which is bounded by n */
    assert(d > 0);
    proof { lemma_division_bound(n, d); }
    let result = n / d;
    result
}
// </vc-code>

}
fn main() {}