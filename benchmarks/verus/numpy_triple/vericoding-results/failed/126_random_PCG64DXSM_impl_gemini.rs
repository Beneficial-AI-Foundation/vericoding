// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed MULTIPLIER and INCREMENT from spec const to const to allow use in exec functions */
const MULTIPLIER: u64 = 6364136223846793005;
const INCREMENT: u64 = 1442695040888963407;

#[inline(always)]
fn pcg_step(state: u64) -> (res: u64) {
    state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT)
}

/* helper modified by LLM (iteration 4): replaced unsupported rotate_right with bitwise operations */
#[inline(always)]
fn pcg_output(state: u64) -> (res: u64) {
    let xorshifted = ((state >> 18) ^ state) >> 27;
    let rot = (state >> 59) as u32;
    (xorshifted >> rot) | (xorshifted << ((64u32 - rot) & 63u32))
}

spec fn state_after_n_steps(seed: u64, n: nat) -> u64
    decreases n
{
    if n == 0 {
        seed
    } else {
        pcg_step(state_after_n_steps(seed, (n - 1) as nat))
    }
}

/* helper modified by LLM (iteration 3): fixed compilation error and defined spec recursively via appending */
spec fn pcg64_concrete_spec(seed: u64, n: nat) -> Seq<u64>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        pcg64_concrete_spec(seed, (n - 1) as nat).push(pcg_output(state_after_n_steps(seed, (n - 1) as nat)))
    }
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
    /* code modified by LLM (iteration 5): no logic change, depending on fixed helper functions */
    let mut results: Vec<u64> = Vec::with_capacity(n);
    let mut state = seed;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            results.len() == i,
            state == state_after_n_steps(seed, i as nat),
            results@ == pcg64_concrete_spec(seed, i as nat),
            forall|j: int| 0 <= j < i ==> results[j] >= 0,
    {
        let output = pcg_output(state);
        results.push(output);
        state = pcg_step(state);
        i = i + 1;
    }
    results
}
// </vc-code>

}
fn main() {}