// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_where(condition: Vec<bool>, x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition@.len() == x@.len(),
        condition@.len() == y@.len(),
    ensures 
        result@.len() == condition@.len(),
        forall|i: int| 0 <= i < condition@.len() ==> 
            (condition@[i] ==> result@[i] == x@[i]) &&
            (!condition@[i] ==> result@[i] == y@[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Added runtime length assertions to prove vector indexing preconditions and updated invariant with length equalities. */
    let n: usize = condition.len();
    assert(n == x.len());
    assert(n == y.len());
    let mut result: Vec<f32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i as int,
            n as int >= 0,
            i as int >= 0,
            condition@.len() == n as int,
            x@.len() == n as int,
            y@.len() == n as int,
            forall |j: int| 0 <= j < i as int ==>
                (condition@[j] ==> result@[j] == x@[j]) &&
                (!condition@[j] ==> result@[j] == y@[j])
        decreases n - i
    {
        let cond = condition[i];
        let val = if cond { x[i] } else { y[i] };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}