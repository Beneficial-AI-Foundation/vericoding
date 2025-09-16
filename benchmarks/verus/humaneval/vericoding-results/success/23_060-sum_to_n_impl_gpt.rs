// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_sum_to_n(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else {
        n + spec_sum_to_n((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_spec_sum_zero()
    ensures
        spec_sum_to_n(0) == 0,
{ }

proof fn lemma_spec_sum_step(n: nat)
    ensures
        spec_sum_to_n(n + 1) == spec_sum_to_n(n) + (n + 1),
{ }
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)

    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0u32 {
        Some(0u32)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}