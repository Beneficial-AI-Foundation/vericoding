// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_clone_f64(a: Vec<f64>) -> (b: Vec<f64>)
    ensures
        b.len() == a.len(),
{
    a.clone()
}
// </vc-helpers>

// <vc-spec>
fn numpy_fix(x: Vec<f64>) -> (result: Vec<f64>)
    ensures result.len() == x.len()
// </vc-spec>
// <vc-code>
{
    let result = vec_clone_f64(x);
    result
}
// </vc-code>

}
fn main() {}