// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed unnecessary contains_at helper now that it's a code block */
// </vc-helpers>

// <vc-spec>
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            // For elements already copied, they should match the original
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;
    }
    assert(result.len() == a.len());
    result
}
// </vc-code>

}
fn main() {}