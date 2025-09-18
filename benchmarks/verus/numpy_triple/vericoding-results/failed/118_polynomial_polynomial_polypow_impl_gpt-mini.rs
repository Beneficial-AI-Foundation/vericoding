// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): polynomial multiplication using usize indices */
fn poly_mul(a: Vec<f32>, b: Vec<f32>) -> Vec<f32> {
    if a.len() == 0 || b.len() == 0 {
        let mut res: Vec<f32> = Vec::new();
        return res;
    }
    let len = a.len() + b.len() - 1;
    let mut res: Vec<f32> = Vec::new();
    let mut i = 0usize;
    while i < len {
        res.push(0.0f32);
        i += 1;
    }
    let mut i = 0usize;
    while i < a.len() {
        let mut j = 0usize;
        while j < b.len() {
            let idx = i + j;
            let v = res[idx];
            res[idx] = v + a[i] * b[j];
            j += 1;
        }
        i += 1;
    }
    res
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
    /* code modified by LLM (iteration 5): use usize exponent and exponentiation by squaring without int/nat */
    let mut exp: usize = pow as usize;
    if exp == 0 {
        let mut res: Vec<f32> = Vec::new();
        res.push(1.0f32);
        return res;
    }
    if exp == 1 {
        return c.clone();
    }
    let mut result: Vec<f32> = Vec::new();
    result.push(1.0f32);
    let mut base: Vec<f32> = c.clone();
    while exp > 0 {
        if exp % 2 == 1 {
            result = poly_mul(result, base.clone());
        }
        exp = exp / 2;
        if exp > 0 {
            base = poly_mul(base.clone(), base.clone());
        }
    }
    result
}
// </vc-code>

}
fn main() {}