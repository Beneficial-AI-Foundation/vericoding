// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to update sum invariant */
proof fn lemma_step(i: u32, acc: u32)
    requires
        acc * 2 == i * (i + 1),
    ensures
        (acc + (i + 1)) * 2 == (i + 1) * (i + 2),
    decreases
        0u32
{
    proof {
        assert((acc + (i + 1)) * 2 == acc * 2 + (i + 1) * 2);
        assert(acc * 2 == i * (i + 1));
        assert(acc * 2 + (i + 1) * 2 == i * (i + 1) + (i + 1) * 2);
        assert(i * (i + 1) + (i + 1) * 2 == (i + 1) * (i + 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): compute sum iteratively and average with proper casts */
    let mut i: u32 = 0u32;
    let mut acc: u32 = 0u32;
    while i < n
        invariant
            acc * 2 == i * (i + 1),
            i <= n,
        decreases n - i
    {
        let old_i = i;
        let old_acc = acc;
        let next = i + 1u32;
        acc = acc + next;
        i = next;
        proof { lemma_step(old_i, old_acc); }
    }
    let sum: u32 = acc;
    let avg: f64 = if n == 0u32 { 0.0 } else { (sum as f64) / (n as f64) };
    (sum, avg)
}
// </vc-code>

}
fn main() {}