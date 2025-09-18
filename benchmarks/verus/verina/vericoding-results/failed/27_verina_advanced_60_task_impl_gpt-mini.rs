// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
{
    /* helper modified by LLM (iteration 5): provides is_even predicate */
    spec fn is_even(n: nat) -> bool { n % 2 == 0 }
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
{
    /* code modified by LLM (iteration 5): build evens and odds by filtering the input sequence and converting to Vec */
    let s = nums@;
    let evens_seq = s.filter(|n: nat| n % 2 == 0);
    let odds_seq = s.filter(|n: nat| n % 2 == 1);
    let evens: Vec<nat> = Vec::from_seq(evens_seq);
    let odds: Vec<nat> = Vec::from_seq(odds_seq);
    (evens, odds)
}
// </vc-code>

}
fn main() {}