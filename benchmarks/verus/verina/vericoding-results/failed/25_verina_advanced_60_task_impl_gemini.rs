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
    /* code modified by LLM (iteration 5): fix mismatched types by using nat literals */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            evens@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0),
            odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1),
        decreases nums.len() - i,
    {
        let num = nums[i];
        if num % 2 == 0 {
            evens.push(num);
        } else {
            odds.push(num);
        }
        i = i + 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}