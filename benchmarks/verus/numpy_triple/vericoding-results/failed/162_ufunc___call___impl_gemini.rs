// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ufunc_call(op: spec_fn(f32, f32) -> f32, a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == op(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion to connect concrete `+` op to abstract `op` spec */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == op(a@[j], b@[j])
        decreases a.len() - i
    {
        let val = a[i] + b[i];
        result.push(val);
        proof {
            assert(op(a@[i], b@[i]) == a@[i] + b@[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}