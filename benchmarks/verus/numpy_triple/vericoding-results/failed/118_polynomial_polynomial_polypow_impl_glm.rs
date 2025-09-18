// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn poly_mul(a: Vec<f32>, b: Vec<f32>) -> (result: Vec<f32>) {
    let len_a = a.len();
    let len_b = b.len();
    if len_a == 0 || len_b == 0 {
        Vec::new()
    } else {
        let mut res = vec![0.0f32; len_a + len_b - 1];
        for i in 0..len_a {
            for j in 0..len_b {
                res[i+j] += a[i] * b[j];
            }
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type mismatches by using nat literals and nat counter */
{
    if pow == 0n {
        vec![1.0f32]
    } else {
        let mut result = c;
        let mut i: nat = 1n;
        while i < pow
            decreases pow - i
        {
            result = poly_mul(result, c);
            i = i + 1n;
        }
        result
    }
}
// </vc-code>

}
fn main() {}