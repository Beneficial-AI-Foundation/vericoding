// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn philox_spec_fn(n: nat, seed: nat) -> Seq<int>;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn philox(n: usize, seed: u64) -> (result: Vec<i32>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> 0 <= result[i] && result[i] < 1000000,
        forall|seed1: u64, seed2: u64| seed1 == seed2 ==> 
            philox_spec_fn(n as nat, seed1 as nat) == philox_spec_fn(n as nat, seed2 as nat)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}