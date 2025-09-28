// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed nat literal syntax by using proper nat(0) and nat(1) */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            evens@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == nat(0)),
            odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == nat(1)),
            forall|j: int| 0 <= j < evens.len() ==> evens[j] % 2 == nat(0),
            forall|j: int| 0 <= j < odds.len() ==> odds[j] % 2 == nat(1),
        decreases nums.len() - i
    {
        if nums[i] % 2 == nat(0) {
            evens.push(nums[i]);
        } else {
            odds.push(nums[i]);
        }
        i += 1;
    }
    
    proof {
        assert(nums@.subrange(0, nums.len() as int) == nums@);
    }
    
    (evens, odds)
}
// </vc-code>

}
fn main() {}