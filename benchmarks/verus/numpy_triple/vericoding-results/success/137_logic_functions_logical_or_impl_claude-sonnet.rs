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
    /* code modified by LLM (iteration 4): strengthened invariant to maintain bounds relationship */
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> j < x1.len() && j < x2.len() && result[j] == (x1[j] || x2[j]),
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(x1.len() == x2.len());
        assert(i < x2.len());
        result.push(x1[i] || x2[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}