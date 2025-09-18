// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < val.len()
        invariant
            0 <= i <= val.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == val[j].1,
        decreases val.len() - i
    {
        result.push(val[i].1);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}