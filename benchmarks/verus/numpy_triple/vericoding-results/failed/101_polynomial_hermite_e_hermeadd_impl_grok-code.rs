// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed, leaving empty as per original */
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced invalid ghost int casts with proper exec usize comparisons for Vec indexing */
    let len = if c1.len() < c2.len() { c2.len() } else { c1.len() };
    let mut result: Vec<i32> = Vec::new();
    for i in 0..len
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> {
                let coeff1_g = if j < c1@.len() { c1@[j] } else { 0 };
                let coeff2_g = if j < c2@.len() { c2@[j] } else { 0 };
                #[trigger] result@[j] == coeff1_g + coeff2_g
            }
    {
        let coeff1 = if i < c1.len() { c1[i] } else { 0 };
        let coeff2 = if i < c2.len() { c2[i] } else { 0 };
        result.push(coeff1 + coeff2);
    }
    result
}
// </vc-code>

}
fn main() {}