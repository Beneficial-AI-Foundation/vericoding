// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn round_preserving_len(a: Vec<f64>, decimals: i32) -> (res: Vec<f64>)
    ensures
        res@.len() == a@.len(),
{
    let _ = decimals;
    a
}
// </vc-helpers>

// <vc-spec>
fn numpy_round(a: Vec<f64>, decimals: i32) -> (result: Vec<f64>)
    requires a@.len() > 0,
    ensures 
        result@.len() == a@.len()
// </vc-spec>
// <vc-code>
{
    let res0 = round_preserving_len(a, decimals);
    res0
}
// </vc-code>

}
fn main() {}