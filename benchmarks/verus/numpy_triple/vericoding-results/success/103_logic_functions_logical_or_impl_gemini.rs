// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn logical_or(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] || x2[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x2[i]) == (x2[i] || x1[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || false) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || true) == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x1[i]) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == true || x2[i] == true) ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == false && x2[i] == false) ==> result[i] == false,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j] || x2@[j]),
        decreases x1.len() - i
    {
        let val = x1[i] || x2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}