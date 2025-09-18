// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper block. */

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
/* code modified by LLM (iteration 5): Corrected type casting for `%` operator. */
{
    let mut evens_vec: Vec<nat> = Vec::new();
    let mut odds_vec: Vec<nat> = Vec::new();

    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|j: int| 0 <= j < evens_vec.len() ==> evens_vec@[j] % 2 == 0,
            forall|j: int| 0 <= j < odds_vec.len() ==> odds_vec@[j] % 2 == 1,
            (evens_vec@ + odds_vec@) =~= (nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0) +
                                           nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1))
        decreases nums.len() - i
    {
        let num_val = nums[i];
        if num_val % 2 == 0 {
            evens_vec.push(num_val);
        } else {
            odds_vec.push(num_val);
        }
        i = i + 1;
    }

    (evens_vec, odds_vec)
}
// </vc-code>

}
fn main() {}