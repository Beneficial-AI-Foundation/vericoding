// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function to convert usize to int for use in specs */
spec fn usize_to_int(u: usize) -> int {
    u as int
}

// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices@.len() ==> 
            indices@[i] < a@.len() && a@[indices@[i] as int] != 0.0,

        forall|i: int| 0 <= i < a@.len() && a@[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] != indices@[j],

        forall|i: int, j: int| 0 <= i < j < indices@.len() ==> 
            indices@[i] < indices@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and maintain invariant proving membership by cases using proof blocks */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i as int <= a@.len(),
            forall|k:int| 0 <= k < i as int ==> (indices@.contains(k as usize) == (a@[k] != 0.0)),
            forall|k:int| 0 <= k < indices@.len() ==> indices@[k] < i as int,
            forall|p:int, q:int| 0 <= p < q < indices@.len() ==> indices@[p] < indices@[q],
        decreases a@.len() - i as int
    {
        let old_i: int = i as int;
        if a[i] != 0.0 {
            indices.push(i);
            proof {
                // after pushing, the new index is contained
                assert(indices@.contains(old_i as usize));
            }
        } else {
            proof {
                // if not pushed, it remains not contained
                assert(!indices@.contains(old_i as usize));
            }
        }
        i = i + 1;
        proof {
            // combine the old invariant for k < old_i and the fact about old_i to get the invariant for the new i
            assert(forall|k:int| 0 <= k < old_i ==> (indices@.contains(k as usize) == (a@[k] != 0.0)));
            assert(indices@.contains(old_i as usize) == (a@[old_i as int] != 0.0));
            assert(forall|k:int| 0 <= k < i as int ==> (indices@.contains(k as usize) == (a@[k] != 0.0)));
        }
    }
    indices
}

// </vc-code>

}
fn main() {}