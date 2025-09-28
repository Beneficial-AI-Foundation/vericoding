// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no-op proof helper to satisfy verifier needs */
proof fn fft_helpers_dummy() {
    // no-op
}

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
    /* code modified by LLM (iteration 5): compute fft frequencies and maintain invariant referencing spec fft_freq_val */
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == fft_freq_val(j, n as int, d),
        decreases n - i
    {
        let val: f64;
        if i < (n + 1) / 2 {
            val = (i as f64) / ((n as f64) * d);
        } else {
            val = ((i as f64) - (n as f64)) / ((n as f64) * d);
        }
        result.push(val);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}