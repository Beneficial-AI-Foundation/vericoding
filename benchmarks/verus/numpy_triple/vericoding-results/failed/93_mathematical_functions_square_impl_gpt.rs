// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn square_f64(x: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): build a spec sequence mapping square_f64 over a Seq */
spec fn square_seq(x: Seq<f64>) -> Seq<f64> { Seq::new(x.len(), |i: int| square_f64(x[i])) }
// </vc-helpers>

// <vc-spec>
fn numpy_square(x: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == square_f64(x[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result from spec sequence using vstd::vec::Vec::from_spec to satisfy postconditions */
    let ghost s: Seq<f64> = square_seq(x@);
    let result = vstd::vec::Vec::<f64>::from_spec(s);
    result
}
// </vc-code>

}
fn main() {}