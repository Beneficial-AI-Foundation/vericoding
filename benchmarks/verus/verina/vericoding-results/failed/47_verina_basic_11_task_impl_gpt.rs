// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix nat/int mismatch for modulus by using (10 as nat) */
spec fn mod10(n: nat) -> nat { n % (10 as nat) }

/* helper modified by LLM (iteration 2): lemma stating bounds and equality for mod10 */
proof fn lemma_mod10_bounds(n: nat)
    ensures
        mod10(n) < (10 as nat),
        mod10(n) == n % (10 as nat)
{
}
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute last digit using nat modulus with explicit cast */
    n % (10 as nat)
}
// </vc-code>

}
fn main() {}