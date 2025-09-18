// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to prove termination of the while loop */
    let mut result = Vec::new();
    result.push(0.0f32);
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i <= c.len(),
            result.view().len() == (i as int) + 1,
            result.view()[0] == 0.0f32,
            forall|j: int| 0 <= j < i as int ==> result.view()[j + 1] == c.view()[j],
        decreases c.len() - i,
    {
        result.push(c[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}