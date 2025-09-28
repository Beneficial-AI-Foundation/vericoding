// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    // code modified by LLM (iteration 2): avoid using int in executable code
    let half = (n + 1) / 2;
    let mut result = Vec::with_capacity(n);

    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as usize] == fft_freq_val(j, n as int, d),
        decreases n - i,
    {
        let val = if i < half {
            (i as f64) / ((n as f64) * d)
        } else {
            (i as f64 - n as f64) / ((n as f64) * d)
        };
        result.push(val);
    }

    result
}
// </vc-code>


}
fn main() {}