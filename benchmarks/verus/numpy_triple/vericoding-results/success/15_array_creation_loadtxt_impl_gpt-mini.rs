// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_len_nonneg<T>(v: &Vec<T>)
    ensures
        v@.len() >= 0,
{
    proof {
        assert(v@.len() >= 0);
    }
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
    // impl-start
    let result: Vec<f64> = Vec::new();
    vec_len_nonneg(&result);
    result
    // impl-end
}
// </vc-code>


}
fn main() {}