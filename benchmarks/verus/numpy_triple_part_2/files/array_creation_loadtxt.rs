// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn loadtxt(fname_len: usize, skiprows: usize) -> (result: Vec<f64>)
    requires 
        fname_len > 0,
        skiprows >= 0,
    ensures
        result.len() >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}