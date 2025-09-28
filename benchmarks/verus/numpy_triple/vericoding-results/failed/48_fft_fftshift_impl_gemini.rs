// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Fix compilation error with ghost variable declaration. */
    let n = x.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result = Vec::new();
    let ghost n_int = n as int;
    let ghost p_int = n_int / 2;
    let ghost shift_int = n_int - p_int;

    let shift = n - n / 2;

    let mut i: usize = 0;
    while i < n
        invariant
            x.len() == n,
            n > 0,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] ==
                x@[((j + shift_int) % n_int) as usize],
        decreases n - i
    {
        let old_idx = (i + shift) % n;

        proof {
            let i_int = i as int;
            let old_idx_int = (i_int + shift_int) % n_int;
            assert(shift as int == shift_int);
            assert((i + shift) as int == i_int + shift_int);
            if n > 0 {
                vstd::arithmetic::mod_internals::mod_positive(i + shift, n);
            }
            assert(old_idx == old_idx_int as usize);
        }
        
        result.push(x[old_idx]);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}