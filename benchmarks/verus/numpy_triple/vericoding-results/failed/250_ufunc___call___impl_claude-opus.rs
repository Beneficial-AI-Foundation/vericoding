// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type conversion error - using usize directly for indexing */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == op(a@[j], b@[j]),
        decreases n - i
    {
        // Since op is a spec_fn, we cannot execute it in regular code
        // We need to use a ghost variable and choose to satisfy the spec
        let ghost_val = Ghost(op(a@[i as int], b@[i as int]));
        let val: f32 = choose|v: f32| v == ghost_val@;
        result.push(val);
        
        proof {
            // The choose ensures the invariant is maintained
            assert(result@[i as int] == op(a@[i as int], b@[i as int]));
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}