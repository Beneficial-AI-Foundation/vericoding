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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < data.len()
        invariant
            0 <= i <= data.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == data[j],
        decreases data.len() - i
    {
        let item = data[i];
        result.push(item);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}