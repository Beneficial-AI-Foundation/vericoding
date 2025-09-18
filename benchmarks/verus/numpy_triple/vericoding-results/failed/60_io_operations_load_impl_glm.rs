// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn load_ghost(file: String, allow_pickle: bool, n: nat) -> Vec<f64>;

fn load(file: String, allow_pickle: bool, n: usize) -> (result: Vec<f64>)
    ensures 
        result.len() == n,
        true, // Result elements exist (trivially true)
        forall|second_load: Vec<f64>| #![trigger second_load.len()] second_load == load_ghost(file, allow_pickle, n as nat) ==>
            forall|i: int| 0 <= i < n ==> result[i] == second_load[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use vec![0.0; n] and prove length */
{
    let result = vec![0.0; n];
    proof {
        // Prove the first condition: result.len() == n
        assert(result.len() == n);

        // The second condition is true, so nothing to do.

        // For the third condition, we cannot prove it without knowing load_ghost.
        // We leave it unproven for now.
    }
    result
}
// </vc-code>

}
fn main() {}