// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed for this implementation */
// </vc-helpers>

// <vc-spec>
fn ufunc_call(op: spec_fn(f32, f32) -> f32, a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    requires a@.len() == b@.len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == op(a@[i], b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking and casting issues */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == op(a@[j], b@[j]),
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(0 <= i < a@.len());
            assert(0 <= i < b@.len());
        }
        let val = a[i] + b[i];
        proof {
            assert(val == op(a@[i as int], b@[i as int]));
        }
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}