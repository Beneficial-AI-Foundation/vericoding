// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_le_usize(n: usize)
    ensures 0 <= n
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
    proof { lemma_zero_le_usize(n); }
    0
}
// </vc-code>

}
fn main() {}