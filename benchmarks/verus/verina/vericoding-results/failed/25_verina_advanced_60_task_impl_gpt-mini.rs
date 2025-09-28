// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parity spec helper and trivial proof */
spec fn is_even(n: nat) -> bool { n % 2 == 0 }
proof fn lemma_partition_dummy() { proof { } }
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
    /* code modified by LLM (iteration 5): partition nums into evens and odds */
    let mut evens: Vec<nat> = Vec::new();
    let mut odds: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    let n: usize = nums.len();
    while i < n
        invariant
            i <= n,
            evens.len() + odds.len() == i,
        decreases n - i
    {
        let x: nat = nums[i];
        if x % 2 == 0 {
            evens.push(x);
        } else {
            odds.push(x);
        }
        i = i + 1;
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}