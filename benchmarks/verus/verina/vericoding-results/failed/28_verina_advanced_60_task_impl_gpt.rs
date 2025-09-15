// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add parity predicates for nat to aid reasoning */
spec fn is_even(n: nat) -> bool { n % 2 == 0 }
/* helper modified by LLM (iteration 2): add odd predicate consistent with even */
spec fn is_odd(n: nat) -> bool { n % 2 == 1 }
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
    /* code modified by LLM (iteration 2): fix nat vs int literal mismatch using 0nat/1nat and implement loop with invariants */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            evens@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0),
            odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1),
            forall|k: int| 0 <= k < evens.len() ==> evens[k] % 2 == 0,
            forall|k: int| 0 <= k < odds.len() ==> odds[k] % 2 == 1
        decreases nums.len() - i
    {
        let n = nums[i];
        if n % 2 == 0nat {
            evens.push(n);
            assert(n % 2 == 0nat);
        } else {
            odds.push(n);
            assert(n % 2 == 1nat);
        }
        i = i + 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}