// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
spec fn square_f64(x: f64) -> f64 {
    x * x
}

fn numpy_square_impl(x: &Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
{
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == square_f64(x[j]),
        decreases x.len() - i
    {
        result.push(square_f64(x[i]));
        i += 1;
    }
    result
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
    numpy_square_impl(&x)
}
// </vc-code>

}
fn main() {}