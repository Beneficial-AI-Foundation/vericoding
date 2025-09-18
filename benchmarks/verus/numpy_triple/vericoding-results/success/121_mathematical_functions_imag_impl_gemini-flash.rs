// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Empty helper section, no changes needed */
// </vc-helpers>

// <vc-spec>
fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i] == val[i].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i].1 == 0.0 ==> result[i] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i].0 != 0.0 || val[i].1 != 0.0 ==> result[i] == val[i].1),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added decreases clause to loop */
{
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < val.len()
        invariant
            0 <= i <= val.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == val[j].1
        decreases val.len() - i
    {
        result_vec.push(val[i].1);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}