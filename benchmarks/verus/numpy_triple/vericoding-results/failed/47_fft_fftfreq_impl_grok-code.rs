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
/* code modified by LLM (iteration 5): computationally obtained frequencies using loop, maintaining invariants for verification */
{
    let mut result = Vec::with_capacity(n);
    let mut i: usize = 0;
    let mid = (n + 1) / 2;
    while i < n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == fft_freq_val(j as int, n as int, d),
        decreases (n - i) as int
    {
        let ii: f64 = i as f64;
        let nn: f64 = n as f64;
        let val = if i < mid {
            ii / (d * nn)
        } else {
            (ii - nn) / (d * nn)
        };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}