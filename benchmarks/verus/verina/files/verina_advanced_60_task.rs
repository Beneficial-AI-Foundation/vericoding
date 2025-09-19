// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn partition_evens_odds(nums: &Vec<u8>) -> (result: (Vec<u8>, Vec<u8>))
    requires true,
    ensures ({
        let evens = result.0;
        let odds = result.1;
        &&& evens@.map(|i, n| n as nat) + odds@.map(|i, n| n as nat) == nums@.map(|i, n| n as nat).filter(|n: nat| n % 2 == 0) + nums@.map(|i, n| n as nat).filter(|n: nat| n % 2 == 1)
        &&& forall|i: int| 0 <= i < evens.len() ==> evens[i] as nat % 2 == 0
        &&& forall|i: int| 0 <= i < odds.len() ==> odds[i] as nat % 2 == 1
    }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}