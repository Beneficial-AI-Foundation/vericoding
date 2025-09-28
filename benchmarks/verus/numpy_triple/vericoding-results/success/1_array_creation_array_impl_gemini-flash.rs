// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed unnecessary `data.len() < 0x8000_0000` precondition. */
fn make_vec_f64(data: &Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
{
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < data.len()
        invariant
            i <= data.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == data[j],
        decreases data.len() - i
    {
        result_vec.push(data[i]);
        i = i + 1;
    }
    result_vec
}
// </vc-helpers>

// <vc-spec>
fn array(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Calls `make_vec_f64` to create the array. */
{
    make_vec_f64(&data)
}
// </vc-code>

}
fn main() {}