// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
spec fn square_f64(x: f64) -> f64 {
    x * x
}

fn exec_square(x: f64) -> (result: f64)
    ensures result == square_f64(x)
{
    x * x
}
// </vc-helpers>

// <vc-spec>
fn numpy_square(x: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j < i as int ==> result@[j] == square_f64(x@[j])
    {
        let val = exec_square(x[i]);
        result.push(val);
    }
    result
}
// </vc-code>

}
fn main() {}