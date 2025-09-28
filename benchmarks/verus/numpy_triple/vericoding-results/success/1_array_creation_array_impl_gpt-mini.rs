// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): clone Vec by iterating and pushing elements */
fn vec_clone(data: &Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
{
    let mut res: Vec<f64> = Vec::new();
    let mut i = 0;
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == data[j],
        decreases data.len() - i
    {
        res.push(data[i]);
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn array(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use vec_clone to produce a copy of input vector */
    vec_clone(&data)
}
// </vc-code>

}
fn main() {}