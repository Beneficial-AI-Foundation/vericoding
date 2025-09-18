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
/* code modified by LLM (iteration 5): Fixed compilation errors by ensuring vector indexing happens using `usize` and adjusting `forall` quantifiers to respect this. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant 
            0 <= i as int && i as int <= x1.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result[j as usize] == (x1[j as usize] == x2[j as usize]),
    {
        result.push(x1[i].clone() == x2[i].clone());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}