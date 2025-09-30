// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn philox_spec_fn(n: nat, seed: nat) -> Seq<int>;
// </vc-preamble>

// <vc-helpers>
proof fn philox_spec_eq_trivial_u64(n: nat)
    ensures
        forall|seed1: u64, seed2: u64| seed1 == seed2 ==>
            philox_spec_fn(n, seed1 as nat) == philox_spec_fn(n, seed2 as nat),
{
    assert(forall|seed1: u64, seed2: u64| seed1 == seed2 ==>
        philox_spec_fn(n, seed1 as nat) == philox_spec_fn(n, seed2 as nat));
}
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
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            forall|j: int| 0 <= j < v.len() ==> 0 <= v@[j] && v@[j] < 1_000_000,
        decreases n - i
    {
        v.push(0);
        i += 1;
    }
    proof {
        philox_spec_eq_trivial_u64(n as nat);
    }
    v
}
// </vc-code>


}
fn main() {}