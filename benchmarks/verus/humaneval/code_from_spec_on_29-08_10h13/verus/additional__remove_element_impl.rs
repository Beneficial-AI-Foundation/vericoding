use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)"
docstring: Implement remove element functionality.
*/
// </vc-description>

// <vc-spec>
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires pos < a.len()
    ensures result@.len() == a@.len() - 1
    ensures forall|i: int| 0 <= i < pos ==> result@[i] == a@[i]
    ensures forall|i: int| pos <= i < result@.len() ==> result@[i] == a@[i + 1]
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result@.len() == if i <= pos { i } else { i - 1 },
            forall|j: int| 0 <= j < result@.len() && j < pos ==> result@[j] == a@[j],
            forall|j: int| pos <= j < result@.len() ==> result@[j] == a@[j + 1],
            pos < a.len()
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}