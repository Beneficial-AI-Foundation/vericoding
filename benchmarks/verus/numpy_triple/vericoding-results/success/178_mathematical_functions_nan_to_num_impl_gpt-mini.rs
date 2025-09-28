// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn noop_helper() {
}

// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    let result = x.clone();
    result
}
// </vc-code>

}
fn main() {}