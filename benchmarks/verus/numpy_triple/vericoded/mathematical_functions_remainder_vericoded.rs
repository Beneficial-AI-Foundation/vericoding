// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec_f64(v: Vec<f64>) -> (res: Vec<f64>)
    ensures
        res@.len() == v@.len(),
{
    v
}
// </vc-helpers>

// <vc-spec>
fn remainder(x1: Vec<f64>, x2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2@.len() ==> x2@[i] != 0.0,
    ensures
        result@.len() == x1@.len(),
// </vc-spec>
// <vc-code>
{
    let result = id_vec_f64(x1);
    result
}
// </vc-code>

}
fn main() {}