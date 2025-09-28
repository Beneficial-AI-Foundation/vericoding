// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove basic properties of a 2-element sequence */
proof fn lemma_two_seq_props(x: f64, y: f64)
    ensures
        seq![x, y].len() == 2,
        seq![x, y][0] == x,
        seq![x, y][1] == y,
{
    let s = seq![x, y];
    assert(s.len() == 2);
    assert(s[0] == x);
    assert(s[1] == y);
}
// </vc-helpers>

// <vc-spec>
fn hermeline(off: f64, scl: f64) -> (coeffs: Vec<f64>)
    ensures
        coeffs@.len() == 2,
        coeffs@[0] == off,
        (scl == 0.0 ==> coeffs@[1] == 0.0),
        (scl != 0.0 ==> coeffs@[1] == scl)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): construct vector [off, scl] explicitly and prove properties */
    let mut coeffs_vec: Vec<f64> = Vec::new();
    coeffs_vec.push(off);
    coeffs_vec.push(scl);
    proof {
        assert(coeffs_vec@.len() == 2);
        assert(coeffs_vec@[0] == off);
        assert(coeffs_vec@[1] == scl);
    }
    coeffs_vec
}
// </vc-code>

}
fn main() {}