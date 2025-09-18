// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant syntax by adjusting parentheses, indentation, and conjunction operators to match Verus documentation examples */
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i <= a.len()
        invariant result@.len() == i
        invariant forall|k: int| 0 <= k < i ==> result@[k] == a@[k] % b@[k]
        decreases(a.len() - i)
    {
        result.push(a[i] % b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}