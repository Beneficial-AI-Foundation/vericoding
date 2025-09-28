// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn less_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1@.len() ==> result@[i] == (x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == true <==> x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == false <==> x1@[i] > x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (x1@[i] == x2@[i] ==> result@[i] == true),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] <= x2@[j]),
        decreases x1.len() - i
    {
        let val = x1[i] <= x2[i];
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}