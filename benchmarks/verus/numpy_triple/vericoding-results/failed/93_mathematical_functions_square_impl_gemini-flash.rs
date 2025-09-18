// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added body to spec function `square_f64` */
spec fn square_f64(x: f64) -> f64 { x * x }
// </vc-helpers>

// <vc-spec>
fn numpy_square(x: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type errors, array access, and `old` usage */
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: nat = 0;
    while i < x.len() as nat
        invariant
            x.len() == old(x.len()),
            0 <= i as int <= x.len() as int,
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> result.view_nth(j) == square_f64(x.view_nth(j)),
    {
        result.push(square_f64(x.view_nth(i as int)));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}