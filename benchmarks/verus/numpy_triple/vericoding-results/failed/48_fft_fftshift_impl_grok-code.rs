// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed for this fix */
// </vc-helpers>

// <vc-spec>
fn fftshift(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i as int] == x[((i + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int)) as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors by using i64 for modulo calculation in executable code */
    let n = x.len();
    let mut result = Vec::with_capacity(n);
    let n_i64 = n as i64;
    let shift = n_i64 / 2;
    for i in 0..n
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> 
                result@.index(j) == x@.index(
                    ((j + (x.len() as int) - (x.len() as int) / 2) % (x.len() as int))
                )
        decreases (n - i)
    {
        let i_i64 = i as i64;
        let idx_int = (i_i64 - shift).rem_euclid(n_i64);
        let idx = idx_int as usize;
        result.push(x[idx]);
    }
    result
}
// </vc-code>


}
fn main() {}