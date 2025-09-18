// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added exec mode and proper Verus syntax */
exec fn multiply_polys(a: Vec<f32>, b: Vec<f32>) -> Vec<f32> {
    let mut result = vec![0.0f32; a.len() + b.len() - 1];
    for i in 0..a.len() {
        for j in 0..b.len() {
            result.set(i + j, result[i + j] + a[i] * b[j]);
        }
    }
    result
}

exec fn copy_poly(c: Vec<f32>) -> Vec<f32> {
    let mut result = vec![0.0f32; c.len()];
    for i in 0..c.len() {
        result.set(i, c[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat literals syntax */
    if pow == 0 {
        vec![1.0f32]
    } else if pow == 1 {
        copy_poly(c)
    } else {
        let mut result = vec![1.0f32];
        let mut base = copy_poly(c);
        let mut exp = pow;
        while exp > 0 {
            if exp % 2 == 1 {
                result = multiply_polys(result, base);
            }
            base = multiply_polys(base, base);
            exp = exp / 2;
        }
        result
    }
}
// </vc-code>

}
fn main() {}