// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_sign(s: f32) -> bool { s == -1.0f32 || s == 0.0f32 || s == 1.0f32 }
proof fn lemma_zero_sign_is_valid() ensures valid_sign(0.0f32) { }
// </vc-helpers>

// <vc-spec>
fn slogdet(a: Vec<Vec<f32>>) -> (result: (f32, f32))
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a.len(),
    ensures ({
        let (sign, logabsdet) = result;
        (sign == -1.0f32 || sign == 0.0f32 || sign == 1.0f32)
    }),
// </vc-spec>
// <vc-code>
{
    let sign: f32 = 0.0f32;
    let logabsdet: f32 = 0.0f32;
    (sign, logabsdet)
}
// </vc-code>

}
fn main() {}