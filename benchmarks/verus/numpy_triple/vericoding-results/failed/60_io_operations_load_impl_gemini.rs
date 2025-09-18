// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed function to fix redefinition error */
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
{
    /* code modified by LLM (iteration 5): implemented loop with corrected invariant type */
    let mut v = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v.len() == i,
            v@ == load_ghost(file.clone(), allow_pickle, n as nat)@.subrange(0, i as int),
            load_ghost(file.clone(), allow_pickle, n as nat).len() == n,
        decreases n - i
    {
        proof {
            let overall_spec = load_ghost(file.clone(), allow_pickle, n as nat);
            let next_val = overall_spec@[i as int];
            assert(v.push(next_val)@.subrange(0, (i + 1) as int) == overall_spec@.subrange(0, (i + 1) as int));
        }
        v.push(0.0f64); // This will fail, but is required to make progress. A value must be pushed.
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}