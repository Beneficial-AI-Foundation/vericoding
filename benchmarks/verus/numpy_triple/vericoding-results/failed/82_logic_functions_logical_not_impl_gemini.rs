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
    /* code modified by LLM (iteration 5): add assert to prove loop invariant */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0),
        decreases x.len() - i,
    {
        let val = x[i] == 0.0;
        result.push(val);
        assert(result@[i as int] == (x@[i as int] == 0.0));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}