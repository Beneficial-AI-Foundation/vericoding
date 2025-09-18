// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> x1[i] == x2[i]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
// </vc-spec>
// <vc-code>
{
        /* code modified by LLM (iteration 5): fix loop invariant with bounds */
        let mut result = Vec::new();
        for i in 0..x1.len()
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < i ==> j < x1.len() && j < x2.len() && result[j] == (x1[j] == x2[j]),
        {
            result.push(x1[i] == x2[i]);
        }
        result
    }
// </vc-code>

}
fn main() {}