// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_empty_vec_f64() -> (v: Vec<f64>)
    ensures
        v@.len() == 0,
{
    let v: Vec<f64> = Vec::new();
    v
}
// </vc-helpers>

// <vc-spec>
fn loadtxt(fname_len: u8, skiprows: u8) -> (result: Vec<f64>)
    requires 
        fname_len as nat > 0,
        skiprows as nat >= 0,
    ensures
        result@.len() >= 0,
// </vc-spec>
// <vc-code>
{
    let v = make_empty_vec_f64();
    v
}
// </vc-code>


}
fn main() {}