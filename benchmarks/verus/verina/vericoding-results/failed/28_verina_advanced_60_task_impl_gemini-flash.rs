// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removing the `0_nat` error in num % 2 and leaving this section blank */
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
/* code modified by LLM (iteration 5): Fixed the `0_nat` compilation error by removing the `_nat` suffix and explicitly casting `0` to a `nat` type. */
{
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();

    for i in 0..nums.len() {
        let num: nat = nums[i];
        if num % 2 == 0 {
            evens.push(num);
        } else {
            odds.push(num);
        }
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}