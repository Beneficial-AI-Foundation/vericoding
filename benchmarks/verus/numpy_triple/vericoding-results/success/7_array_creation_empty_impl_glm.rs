// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn empty(n: u8) -> (result: Vec<f64>)
    ensures result.len() == n as usize
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.resize(n as usize, 0.0);
    result
}
// </vc-code>


}
fn main() {}