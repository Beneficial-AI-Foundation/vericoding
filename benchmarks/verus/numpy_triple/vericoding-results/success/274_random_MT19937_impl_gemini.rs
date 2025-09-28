// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mt19937(seed: u32) -> (state: Vec<u32>)
    ensures
        /* The state vector has the correct size (624 elements) */
        state@.len() == 624,
        /* The first element equals the seed */
        state@[0] == seed,
        /* State initialization follows MT19937 recurrence relation */
        forall|i: int| 0 <= i < 623 ==> #[trigger] state@[i] == state@[i] && {
            let k = i + 1;
            let prev_state = state@[i];
            let shifted = prev_state >> 30;
            let xor_result = prev_state ^ shifted;
            let mult_result = 1812433253u32.wrapping_mul(xor_result);
            let next_val = mult_result.wrapping_add(k as u32);
            state@[k] == next_val
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added trigger to loop invariant */
    let mut state = Vec::<u32>::new();
    state.push(seed);

    let mut i: usize = 0;
    while i < 623
        invariant
            0 <= i <= 623,
            state@.len() == i + 1,
            state@[0] == seed,
            forall|j: int| 0 <= j < i ==> #[trigger] state@[j] == state@[j] && {
                let k = j + 1;
                let prev_state = state@[j];
                let shifted = prev_state >> 30;
                let xor_result = prev_state ^ shifted;
                let mult_result = 1812433253u32.wrapping_mul(xor_result);
                let next_val = mult_result.wrapping_add(k as u32);
                state@[k] == next_val
            },
        decreases 623 - i
    {
        let prev_state = state[i];
        let k = i + 1;

        let shifted = prev_state >> 30;
        let xor_result = prev_state ^ shifted;
        let mult_result = 1812433253u32.wrapping_mul(xor_result);
        let next_val = mult_result.wrapping_add(k as u32);
        
        state.push(next_val);
        i = i + 1;
    }

    state
}
// </vc-code>


}
fn main() {}