use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)"
docstring: Implement array concat functionality.
*/
// </vc-description>

// <vc-spec>
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result@.len() == a@.len() + b@.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == a@[i],
        forall|i: int| 0 <= i < b@.len() ==> result@[a@.len() + i] == b@[i]
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j]
        decreases a@.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    
    let mut j = 0;
    while j < b.len()
        invariant
            /* code modified by LLM (iteration 5): corrected invariant to use j as int for proper length calculation */
            0 <= j <= b@.len(),
            result@.len() == a@.len() + j as int,
            forall|k: int| 0 <= k < a@.len() ==> result@[k] == a@[k],
            forall|k: int| 0 <= k < j as int ==> result@[a@.len() + k] == b@[k]
        decreases b@.len() - j
    {
        result.push(b[j]);
        j += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}