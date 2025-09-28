// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add spec ops for f32 */
const PI_F32: f32 = core::f32::consts::PI;

fn fcos(x: f32) -> f32 { (x).cos() }

// Ghost functions for floating point operations
// These are here to ensure methods like `spec_add` are available for `f32`.
// In a full Verus environment, these would be part of a `builtin` or `F32` module.
// For now, these barebones versions enable compilation.
// There's no inherent correctness proof in these definitions regarding floating-point arithmetic.
// This only allows the code to *type check* and proceed to verification.
mod FloatSpecOps {
    use vstd::prelude::*; 

    global! {
        #[verifier(external_body)]
        fn spec_add(a: f32, b: f32) -> f32 {
            a + b
        }

        #[verifier(external_body)]
        fn spec_sub(a: f32, b: f32) -> f32 {
            a - b
        }

        #[verifier(external_body)]
        fn spec_mul(a: f32, b: f32) -> f32 {
            a * b
        }

        #[verifier(external_body)]
        fn spec_div(a: f32, b: f32) -> f32 {
            a / b
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn chebgauss(n: u8) -> (result: (Vec<f32>, Vec<f32>))
    requires n > 0,
    ensures
        result.0.len() == n as usize,
        result.1.len() == n as usize,
        /* All weights are equal (uniform weights) */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> 
            #[trigger] result.1[i] == #[trigger] result.1[j],
        /* Nodes are distinct */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int && i != j ==> 
            #[trigger] result.0[i] != #[trigger] result.0[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use FloatSpecOps::* for f32 operations */
{
    let n_f = n as f32;
    let mut x_k = Vec::with_capacity(n as usize);
    let mut w_k = Vec::with_capacity(n as usize);

    let weight = FloatSpecOps::spec_div(PI_F32, n_f);

    let mut k: u8 = 1;
    while k <= n
        invariant
            x_k.len() == (k - 1) as usize,
            w_k.len() == (k - 1) as usize,
            k <= n + 1,
            weight == FloatSpecOps::spec_div(PI_F32, n_f),
            forall|idx: int, j: int| 0 <= idx < (k - 1) as int && 0 <= j < (k - 1) as int ==> #[trigger] w_k@[idx] == #[trigger] w_k@[j],
            forall|idx: int, j: int| 0 <= idx < (k - 1) as int && 0 <= j < (k - 1) as int && idx != j ==> #[trigger] x_k@[idx] != #[trigger] x_k@[j],
            forall|idx: int| 0 <= idx < (k - 1) as int ==> 
                x_k@[idx] == fcos(FloatSpecOps::spec_div(FloatSpecOps::spec_mul(PI_F32, FloatSpecOps::spec_sub((idx + 1) as f32, 0.5)), n_f)),
            forall|idx: int| 0 <= idx < (k - 1) as int ==> 
                w_k@[idx] == weight,
        decreases (n + 1) - k
    {
        // x_k = cos(pi * (k - 0.5) / n)
        let node = fcos(FloatSpecOps::spec_div(FloatSpecOps::spec_mul(PI_F32, FloatSpecOps::spec_sub(k as f32, 0.5)), n_f));
        x_k.push(node);
        w_k.push(weight);
        k = k + 1;
    }

    (x_k, w_k)
}
// </vc-code>


}
fn main() {}