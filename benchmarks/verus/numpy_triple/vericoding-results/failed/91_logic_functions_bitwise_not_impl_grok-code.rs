// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed spec access by using x@ and result@ for ghost invariants and asserts, and cast i to int for indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] as int == -(x@[k] as int + 1),
        decreases x.len() - i
    {
        let new_val = !x[i];
        proof {
            assert(new_val as int == -(x@[i as int] as int + 1));
        }
        result.push(new_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}