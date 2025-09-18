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
    /* code modified by LLM (iteration 5): fixed type mismatch by casting val to int for modulo operation */
    let mut evens = Vec::<nat>::new();
    let mut odds = Vec::<nat>::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i as int && i as int <= nums.len() as int,
            evens@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0),
            odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1),
            forall|ii: int| 0 <= ii < evens.len() ==> evens[ii] % 2 == 0,
            forall|ii: int| 0 <= ii < odds.len() ==> odds[ii] % 2 == 1,
    {
        let val = nums[i];
        let is_even = (val as int % 2) == 0;
        if is_even {
            evens.push(val);
        } else {
            odds.push(val);
        }
        i = i + 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}