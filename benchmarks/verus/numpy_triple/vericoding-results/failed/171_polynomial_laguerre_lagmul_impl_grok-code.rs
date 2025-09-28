// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1@.len() > 0 && c2@.len() > 0,
    ensures 
        result@.len() == c1@.len() + c2@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> 
            (result@[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1@.len() && 
                    0 <= k < c2@.len() && 
                    j + k == i && 
                    c1@[j] != 0.0 && 
                    c2@[k] != 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clauses to while loops to ensure termination */
{
    let mut result: Vec<f64> = Vec::with_capacity(c1.len() + c2.len() - 1);
    for i in 0..c1.len() {
        for j in 0..c2.len() {
            let idx = i + j;
            while result.len() <= idx
                decreases (idx as int - result.len() as int)
            {
                result.push(0.0);
            }
            result[idx] = result[idx] + c1[i] * c2[j];
        }
    }
    // Ensure length
    while result.len() < c1.len() + c2.len() - 1
        decreases ((c1.len() + c2.len() - 1) as int - result.len() as int)
    {
        result.push(0.0);
    }
    proof {
        assert(result@.len() == c1@.len() + c2@.len() - 1);
    }
    result
}
// </vc-code>

}
fn main() {}