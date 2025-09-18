// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type casting and added proper ghost code handling */
spec fn is_even(n: nat) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: nat) -> bool {
    n % 2 == 1
}

proof fn filter_lemma(s: Seq<nat>, p: spec_fn(nat) -> bool) 
    ensures s.filter(p).len() == s.filter(|i: nat| p(i)).len()
{
    // This lemma is trivial in Verus for sequences
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
/* code modified by LLM (iteration 5): Fixed nat modulo operation using ghost specification functions */
{
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    
    let mut i: usize = 0;
    while i < nums.len() 
        invariant 
            i <= nums.len(),
            evens@.len() + odds@.len() == i,
            forall|j: int| 0 <= j < evens.len() ==> is_even(evens@[j]),
            forall|j: int| 0 <= j < odds.len() ==> is_odd(odds@[j]),
            evens@ + odds@ == nums@.subrange(0, i as int).filter(|n: nat| is_even(n)) + nums@.subrange(0, i as int).filter(|n: nat| is_odd(n))
    {
        let num = nums[i];
        proof {
            if is_even(num) {
                assert(num % 2 == 0);
            } else {
                assert(num % 2 == 1);
            }
        }
        if is_even(num) {
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