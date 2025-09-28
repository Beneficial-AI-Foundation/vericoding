// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No changes needed, helper is correct. */
fn min_f32(a: f32, b: f32) -> (r: f32)
    ensures
        r == a || r == b,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn minimum(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] == x1@[i] || result@[i] == x2@[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Removed failing invariant that used f32 comparison in spec context. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == x1@[j] || result@[j] == x2@[j]),
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        let min_val = if val1 <= val2 { val1 } else { val2 };
        result.push(min_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}