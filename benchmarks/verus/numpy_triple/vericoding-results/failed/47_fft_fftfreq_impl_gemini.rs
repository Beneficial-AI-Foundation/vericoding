// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Removed function definition to resolve compilation error.] */
// </vc-helpers>

// <vc-spec>
spec fn fft_freq_val(i: int, n: int, d: f64) -> f64;

fn fftfreq(n: usize, d: f64) -> (result: Vec<f64>)
    requires 
        n > 0,
        d != 0.0,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < ((n as int + 1) / 2) ==> 
            result[i as int] == fft_freq_val(i, n as int, d),
        forall|i: int| ((n as int + 1) / 2) <= i < n as int ==>
            result[i as int] == fft_freq_val(i, n as int, d),
        result[0] == 0.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [This logic is correct, the fix was removing the conflicting helper function] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let n_f64 = n as f64;
    let d_n_f64 = d * n_f64;

    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == fft_freq_val(j, n as int, d),
        decreases n - i
    {
        let val = if i < (n + 1) / 2 {
            (i as f64) / d_n_f64
        } else {
            ((i as f64) - n_f64) / d_n_f64
        };
        
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}