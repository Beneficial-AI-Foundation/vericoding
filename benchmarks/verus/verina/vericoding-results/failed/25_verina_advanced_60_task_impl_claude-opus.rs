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
    /* code modified by LLM (iteration 5): Fixed nat comparison by casting to int */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            evens@ == nums@.take(i as int).filter(|n: nat| n % 2 == 0),
            odds@ == nums@.take(i as int).filter(|n: nat| n % 2 == 1),
            forall|j: int| 0 <= j < evens.len() ==> evens[j] % 2 == 0,
            forall|j: int| 0 <= j < odds.len() ==> odds[j] % 2 == 1,
    {
        let n = nums[i];
        if (n as int) % 2 == 0 {
            evens.push(n);
        } else {
            odds.push(n);
        }
        i = i + 1;
    }
    
    proof {
        assert(i == nums.len());
        assert(nums@.take(nums.len() as int) == nums@);
        assert(evens@ == nums@.filter(|n: nat| n % 2 == 0));
        assert(odds@ == nums@.filter(|n: nat| n % 2 == 1));
    }
    
    (evens, odds)
}
// </vc-code>

}
fn main() {}