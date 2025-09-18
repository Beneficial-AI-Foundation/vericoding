// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add decreases clause to while loop */
fn array_helper(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
{
    let mut result = Vec::new();
    let mut index = 0;
    while index < data.len()
        invariant
            0 <= index <= data.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == data[i],
        decreases data.len() - index,
    {
        result.push(data[index]);
        index += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn array(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): call helper function with proper decreases clause */
{
    array_helper(data)
}
// </vc-code>

}
fn main() {}