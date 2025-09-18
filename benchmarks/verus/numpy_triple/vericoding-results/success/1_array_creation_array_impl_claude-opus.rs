// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array(data: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == data.len(),
        forall|i: int| 0 <= i < data.len() ==> result[i] == data[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < data.len()
        invariant
            i <= data.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == data[j],
        decreases data.len() - i
    {
        result.push(data[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}