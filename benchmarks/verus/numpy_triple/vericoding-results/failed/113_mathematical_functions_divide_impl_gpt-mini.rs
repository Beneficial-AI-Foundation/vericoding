// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): safe runtime index and division */
fn get_div(x1: &Vec<f32>, x2: &Vec<f32>, i: usize) -> (result: f32)
    requires
        i < x1.len(),
        i < x2.len(),
{
    let r: f32 = x1[i] / x2[i];
    r
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement vectorized division using helper with proofs for bounds */
    let mut result: Vec<f32> = Vec::new();
    let n: usize = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
        decreases n - i
    {
        proof {
            assert(n == x1.len());
            assert(x1.len() == x2.len());
            assert(i < n);
            assert(i < x1.len());
            assert(i < x2.len());
        }
        let v = get_div(&x1, &x2, i);
        result.push(v);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}