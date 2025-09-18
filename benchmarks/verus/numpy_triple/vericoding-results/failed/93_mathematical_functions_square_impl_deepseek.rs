// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>


spec fn square_f64(x: f64) -> f64 {
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
    /* code modified by LLM (iteration 5): added curly braces to loop invariant */
    let mut result = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant {
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == square_f64(x[j])
        }
        decreases x.len() - i
    {
        let squared = square_f64(x[i]);
        result.push(squared);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}