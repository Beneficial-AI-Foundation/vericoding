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
/* code modified by LLM (iteration 5): Fixed the invariant regarding the `forall` quantifier. The index `x1@[j as int]` and `x2@[j as int]` when using the sequence view does not require `0 <= j < i`, but rather `0 <= j < x1.len()` and `0 <= j < x2.len()`, respectively. */
{
    let mut result_vec: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < x1.len()
        invariant 
            result_vec.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result_vec[j as int] == (x1@[j as int] == x2@[j as int]),
        decreases x1.len() - i
    {
        let are_equal = x1[i] == x2[i];
        result_vec.push(are_equal);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}