// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn poly_multiply(a: Seq<f32>, b: Seq<f32>) -> Seq<f32>
    decreases a.len() + b.len()
{
    if a.len() == 0 || b.len() == 0 {
        seq![]
    } else {
        /* helper modified by LLM (iteration 5): removed f32 operations in spec context */
        seq![]
    }
}

fn multiply_polynomials(a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    ensures result.len() == if a.len() == 0 || b.len() == 0 { 0 } else { a.len() + b.len() - 1 }
{
    if a.len() == 0 || b.len() == 0 {
        return Vec::new();
    }
    let mut result = vec![0.0f32; a.len() + b.len() - 1];
    for i in 0..a.len() {
        for j in 0..b.len() {
            result.set(i + j, result[i + j] + a[i] * b[j]);
        }
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
    /* code modified by LLM (iteration 5): fixed nat literals to use as nat cast */
    if pow == 0 as nat {
        vec![1.0f32]
    } else if pow == 1 as nat {
        c.clone()
    } else {
        let half_pow = pow / (2 as nat);
        let half_result = polypow(c.clone(), half_pow);
        let squared = multiply_polynomials(&half_result, &half_result);
        if pow % (2 as nat) == 0 as nat {
            squared
        } else {
            multiply_polynomials(&squared, &c)
        }
    }
}
// </vc-code>

}
fn main() {}