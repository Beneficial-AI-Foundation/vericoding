use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)"
docstring: Implement array copy functionality.
*/
// </vc-description>

// <vc-spec>
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures result@ == a@
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j]
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}