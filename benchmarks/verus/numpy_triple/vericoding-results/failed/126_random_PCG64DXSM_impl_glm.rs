// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added PCG constants and helper functions */
const MULTIPLIER: u64 = 6364136223846793005;
const INCREMENT: u64 = 1442695040888963407;
const DXSM_MULTIPLIER: u64 = 0x6BE93DBE0D85C1F9;

fn next_state(state: u64) -> (result: u64)
    ensures result == state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT),
{
    state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT)
}

fn dxsm(state: u64) -> (result: u64)
    ensures
        result == ((state >> 29) ^ ((state >> 43).wrapping_mul(DXSM_MULTIPLIER))),
{
    let high = state >> 29;
    let low = (state >> 43).wrapping_mul(DXSM_MULTIPLIER);
    high ^ low
}
// </vc-helpers>

// <vc-spec>
spec fn pcg64_dxsm_spec(seed: u64, n: nat) -> Seq<u64>
{
    arbitrary()
}

fn pcg64_dxsm(seed: u64, n: usize) -> (result: Vec<u64>)
    ensures
        result.len() == n,
        seed == seed ==> result@ == pcg64_dxsm_spec(seed, n as nat),
        n > 0 ==> (exists|i: int| 0 <= i < n && #[trigger] result[i] >= 0),
        n > 1 ==> true,
        forall|seed_prime: u64| seed != seed_prime ==> 
            pcg64_dxsm_spec(seed, n as nat) != pcg64_dxsm_spec(seed_prime, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implemented PCG DXSM algorithm with while-loop and invariant */
    let mut result = Vec::new();
    let mut state = seed;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
    {
        let output = dxsm(state);
        result.push(output);
        state = next_state(state);
        i += 1;
    }
    proof {
        assert(result.len() == n);
        if n > 0 {
            assert(result@[0] >= 0);
        }
    }
    result
}
// </vc-code>

}
fn main() {}