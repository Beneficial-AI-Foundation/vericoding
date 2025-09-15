// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_even(n: nat) -> bool {
    n % 2 == 0
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
    /* code modified by LLM (iteration 5): fix nat literal syntax */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    
    for i in 0..nums.len()
        invariant
            evens@.len() + odds@.len() == i,
            evens@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0),
            odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1),
            forall|j: int| 0 <= j < evens.len() ==> evens[j] % 2 == 0,
            forall|j: int| 0 <= j < odds.len() ==> odds[j] % 2 == 1
    {
        if nums[i] % 2 == 0 {
            evens.push(nums[i]);
        } else {
            odds.push(nums[i]);
        }
    }
    
    (evens, odds)
}
// </vc-code>

}
fn main() {}