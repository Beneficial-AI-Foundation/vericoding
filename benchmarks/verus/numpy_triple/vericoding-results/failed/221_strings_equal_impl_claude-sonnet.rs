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
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast i to int in invariant for proper verification */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == (x1[j as int] == x2[j as int]),
        decreases x1.len() - i
    {
        let are_equal = x1[i] == x2[i];
        result.push(are_equal);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}