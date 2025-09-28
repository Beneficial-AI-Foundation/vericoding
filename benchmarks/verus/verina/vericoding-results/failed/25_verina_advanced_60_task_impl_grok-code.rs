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
    /* code modified by LLM (iteration 4): fixed compilation errors by using usize for index, removed invalid suffixes, adjusted invariant to use subrange and nat conversions */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let len: usize = nums.len();
    while i < len
        invariant
            0 <= i@ <= len@,
            evens@ + odds@ == nums@.subrange(0, i as nat).filter(|n: nat| n % 2 == 0) + nums@.subrange(0, i as nat).filter(|n: nat| n % 2 == 1),
            evens@.len() == i as nat,
            forall|j: usize| j < evens.len() ==> #[trigger] evens@[j as nat] % 2 == 0,
            forall|j: usize| j < odds.len() ==> #[trigger] odds@[j as nat] % 2 == 1
        decreases (len - i)@
    {
        let num = nums[i];
        if num % 2 == 0 {
            evens.push(num);
        } else {
            odds.push(num);
        }
        i += 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}