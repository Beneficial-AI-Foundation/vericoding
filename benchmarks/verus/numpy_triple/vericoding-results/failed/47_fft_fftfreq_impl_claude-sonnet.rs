// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate definition and used correct uninterp syntax */
spec fn fft_freq_val(i: int, n: int, d: f64) -> f64;
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
    /* code modified by LLM (iteration 5): removed int casts from exec code and used direct usize arithmetic */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> result[j] == fft_freq_val(j, n as int, d),
    {
        let freq = if i < (n + 1) / 2 {
            (i as f64) / (d * (n as f64))
        } else {
            ((i as isize - n as isize) as f64) / (d * (n as f64))
        };
        result.push(freq);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}