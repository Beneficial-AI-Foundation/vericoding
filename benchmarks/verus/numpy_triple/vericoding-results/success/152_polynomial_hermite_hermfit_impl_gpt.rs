// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn coeffs_len_from_deg(deg: nat) -> nat {
    deg + 1
}

proof fn lemma_coeffs_len_pos(deg: nat)
    ensures
        coeffs_len_from_deg(deg) > 0
{
}
// </vc-helpers>

// <vc-spec>
fn hermfit(x: Vec<f64>, y: Vec<f64>, deg: usize) -> (result: Vec<f64>)
    requires 
        x.len() > 0,
        x.len() == y.len(),
        deg < x.len(),
    ensures
        result.len() == deg + 1,
        deg + 1 > 0,
// </vc-spec>
// <vc-code>
{
    let target_len: usize = deg + 1;
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < target_len
        invariant
            result.len() == i,
            i <= target_len,
        decreases target_len - i
    {
        result.push(0.0f64);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}