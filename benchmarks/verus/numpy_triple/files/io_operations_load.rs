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
        forall|i: int| 0 <= i < n ==> exists|stored_val: f64| result[i] == stored_val,
        forall|second_load: Vec<f64>| (#[trigger] second_load == load_ghost(file, allow_pickle, n as nat)) ==>
            forall|i: int| 0 <= i < n ==> result[i] == second_load[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}