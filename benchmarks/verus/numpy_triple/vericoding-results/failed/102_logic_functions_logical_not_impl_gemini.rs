// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [add broadcast_forall for f64 equality reflexivity] */
    proof {
        broadcast_forall|val: f64| (val == 0.0) == (val == 0.0);
    }

    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x@[j] == 0.0),
        decreases x.len() - i
    {
        let b = x[i] == 0.0;
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}