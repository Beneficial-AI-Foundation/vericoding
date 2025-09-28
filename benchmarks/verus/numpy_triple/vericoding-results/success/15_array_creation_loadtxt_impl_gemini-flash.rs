// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    let result: Vec<f64> = Vec::new();
    result
}
// </vc-code>


}
fn main() {}