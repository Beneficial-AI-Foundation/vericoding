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
    /* code modified by LLM (iteration 5): Fixed assertion by correctly referencing the pushed value */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0)
        decreases x.len() - i
    {
        let val = x[i];
        let bool_val = val == 0.0;
        result.push(bool_val);
        
        assert(result@.len() == i + 1);
        assert(result@[i as int] == bool_val);
        assert(bool_val == (x@[i as int] == 0.0));
        assert(forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0));
        
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}