// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): trivial reflexivity for f32 */
fn f32_refl(a: f32)
    ensures
        a == a,
{
}

// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate over x and copy elements to result with int-indexed invariant */
    let mut result: Vec<f32> = Vec::<f32>::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == x[j],
        decreases (x.len() as int) - (i as int)
    {
        result.push(x[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}