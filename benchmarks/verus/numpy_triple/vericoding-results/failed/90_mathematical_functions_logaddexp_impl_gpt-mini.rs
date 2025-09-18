// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn logaddexp_value(x1: f64, x2: f64) -> f64;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): index-in-range predicate for vectors using nat */
spec fn idx_in_range(len: nat, i: nat) -> bool { i < len }
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
{
    /* code modified by LLM (iteration 5): implement element-wise logaddexp using nat indices and proper invariants */
    let mut i: nat = 0;
    let mut result_vec: Vec<f64> = Vec::new();
    while i < x1.len()
        invariant i <= x1.len();
        invariant result_vec.len() == i;
        invariant forall |j: nat| j < i ==> result_vec[j] == logaddexp_value(x1[j], x2[j]);
        decreases x1.len() - i;
    {
        result_vec.push(logaddexp_value(x1[i], x2[i]));
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}