// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed */
// </vc-helpers>

// <vc-spec>
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): fixed compilation error by using exec types for runtime variables and native usize types instead of ghost int in loop condition */
    #[verifier::exec] let mut result: Vec<T> = Vec::new();
    #[verifier::exec] let mut i: usize = 0;
    while i < a.len()
        invariant
            i@ <= a@.len(),
            result@.len() == i@,
            forall|j: int| 0 <= j < i@ ==> result@[j] == a@[j]
        decreases a@.len() - i@
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}