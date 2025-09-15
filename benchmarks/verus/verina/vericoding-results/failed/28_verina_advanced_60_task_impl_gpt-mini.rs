// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for even numbers */
spec fn is_even(x: nat) -> bool { x % 2 == 0 }
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
    /* code modified by LLM (iteration 5): iterate nums and partition evens/odds with correct seq slicing and invariants */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: int = 0;
    while i < nums@.len()
        invariant 0 <= i && i <= nums@.len()
        invariant evens@ + odds@ == (nums@)[0..i]
        invariant forall |j: int| 0 <= j < evens@.len() ==> evens@[j] % 2 == 0
        invariant forall |j: int| 0 <= j < odds@.len() ==> odds@[j] % 2 == 1
        decreases nums@.len() - i
    {
        let idx: nat = i as nat;
        let v: nat = nums[idx];
        if is_even(v) {
            evens.push(v);
        } else {
            odds.push(v);
        }
        i = i + 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}