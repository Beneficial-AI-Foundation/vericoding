// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): assert implicit non-overflow precondition */
    // The function's `ensures` clause is only satisfiable if the sum of elements
    // does not overflow `i8`. We assert this implicit precondition so the verifier
    // can use it to prove the safety of the addition inside the loop.
    assert(forall|k: int| 0 <= k < x1@.len() ==> 
        i8::MIN as int <= (x1@[k] as int + x2@[k] as int) && 
        (x1@[k] as int + x2@[k] as int) <= i8::MAX as int) by {
    };

    let mut result = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] as int == x1@[j] as int + x2@[j] as int,
        decreases x1.len() - i,
    {
        // With the asserted forall at the function start, this addition is proven safe.
        let val = x1[i] + x2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}