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
    /* code modified by LLM (iteration 5): fixed compilation error by removing @x assignment and using x@[i] directly */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < x.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0),
        decreases (x.len() - i) as nat
    {
        result.push(x@[i] == 0.0);
        proof {
            assert(result@[i] == (x@[i] == 0.0));
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}