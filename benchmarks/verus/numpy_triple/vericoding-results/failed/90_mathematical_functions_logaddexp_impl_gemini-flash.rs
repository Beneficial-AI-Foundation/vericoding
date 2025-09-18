// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add uninterp to spec fn. */
uninterp spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-helpers>

// <vc-spec>
fn logaddexp(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            result[i] == logaddexp_value(x1[i], x2[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected Vec indexing from usize to int in ghost code to prevent compilation errors and conform to Verus slice type constraints. */
{
    let mut result: Vec<f64> = Vec::new();
    let len_int = x1.len() as int;
    
    let mut i: int = 0;
    while i < len_int
        invariant
            0 <= i && i <= len_int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result.finite_core_seq()[j] == logaddexp_value(x1.finite_core_seq()[j], x2.finite_core_seq()[j]),
            x1.len() == len_int,
            x2.len() == len_int,
    {
        result.push(logaddexp_value(x1.finite_core_seq()[i], x2.finite_core_seq()[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}