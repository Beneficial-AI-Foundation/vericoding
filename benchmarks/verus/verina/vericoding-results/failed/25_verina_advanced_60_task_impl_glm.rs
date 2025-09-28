// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed to spec functions to work with nat */
spec fn is_even(n: nat) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: nat) -> bool {
    n % 2 == 1
}
// </vc-helpers>

// <vc-spec>
fn partition_evens_odds(nums: &Vec<nat>) -> (result: (Vec<nat>, Vec<nat>))
    requires true,
    ensures ({
        let evens = result.0;
        let odds = result.1;
        &&& evens@ + odds@ == nums@.filter(|n: nat| n % 2 == 0) + nums@.filter(|n: nat| n % 2 == 1)
        &&& forall|i: int| 0 <= i < evens.len() ==> evens[i] % 2 == 0
        &&& forall|i: int| 0 <= i < odds.len() ==> odds[i] % 2 == 1
    }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implemented using ghost operations */
{
    let evens_seq = nums@.filter(|n: nat| is_even(n));
    let odds_seq = nums@.filter(|n: nat| is_odd(n));
    (evens_seq.to_vec(), odds_seq.to_vec())
}
// </vc-code>

}
fn main() {}