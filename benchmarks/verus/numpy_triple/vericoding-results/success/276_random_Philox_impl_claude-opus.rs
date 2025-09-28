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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result: Vec<i32> = Vec::new();
    let mut state = seed;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= result[j] && result[j] < 1000000,
        decreases n - i
    {
        state = ((state.wrapping_mul(1103515245)).wrapping_add(12345)) & 0x7fffffff;
        let value = (state % 1000000) as i32;
        result.push(value);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}