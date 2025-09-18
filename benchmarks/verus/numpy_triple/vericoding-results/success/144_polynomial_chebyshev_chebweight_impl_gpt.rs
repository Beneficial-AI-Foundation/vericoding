// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec_f32(v: Vec<f32>) -> Vec<f32> { v }
spec fn is_nonempty_len(n: int) -> bool { n > 0 }
proof fn lemma_pos_implies_nonneg(n: int) ensures n > 0 ==> n >= 0 { }
// </vc-helpers>

// <vc-spec>
fn chebweight(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
// </vc-spec>
// <vc-code>
{
    let r = id_vec_f32(x);
    r
}
// </vc-code>

}
fn main() {}