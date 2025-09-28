// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn filter_even_proof(nums: Seq<nat>, i: int) -> (evens: Seq<nat>, odds: Seq<nat>)
    requires 0 <= i <= nums.len()
    ensures evens + odds == nums.filter(|n: nat| n % 2 == 0) + nums.filter(|n: nat| n % 2 == 1)
    ensures forall|j: int| 0 <= j < evens.len() ==> evens[j] % 2 == 0
    ensures forall|j: int| 0 <= j < odds.len() ==> odds[j] % 2 == 1
{
    if i == 0 {
        (Seq::empty(), Seq::empty())
    } else {
        let (mut evens, mut odds) = filter_even_proof(nums, i - 1);
        if nums[i - 1] % 2 == 0 {
            evens = evens + Seq::new(1, |j: int| nums[i - 1]);
        } else {
            odds = odds + Seq::new(1, |j: int| nums[i - 1]);
        }
        (evens, odds)
    }
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
{
    let mut evens = Vec::new();
    let mut odds = Vec::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            evens@ + odds@ == nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 0) + nums@.subrange(0, i as int).filter(|n: nat| n % 2 == 1),
            forall|j: int| 0 <= j < evens.len() ==> evens[j] % 2 == 0,
            forall|j: int| 0 <= j < odds.len() ==> odds[j] % 2 == 1
    {
        if nums[i] % 2 == 0 {
            evens.push(nums[i]);
        } else {
            odds.push(nums[i]);
        }
        i += 1;
    }
    proof {
        let (spec_evens, spec_odds) = filter_even_proof(nums@, nums.len() as int);
        assert(evens@ == spec_evens);
        assert(odds@ == spec_odds);
    }
    (evens, odds)
}
// </vc-code>

}
fn main() {}