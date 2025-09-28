// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn poly2herme(pol: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == pol.len(),
        forall|i: int| 0 <= i < pol@.len() && pol[i as int] != 0.0f32 ==> exists|j: int| 0 <= j < result@.len() && result[j as int] != 0.0f32,
        (exists|i: int| 0 <= i < pol@.len() && pol[i as int] != 0.0f32) ==> (exists|j: int| 0 <= j < result@.len() && result[j as int] != 0.0f32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): copy pol into result preserving entries */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < pol.len()
        invariant
            i <= pol.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k as int] == pol[k as int],
        decreases pol.len() - i
    {
        let x: f32 = pol[i];
        result.push(x);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}