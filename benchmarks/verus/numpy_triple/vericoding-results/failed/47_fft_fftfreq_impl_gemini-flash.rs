// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Marked `fft_freq_val` as `uninterp` and simplified. */
uninterp spec fn fft_freq_val(i: int, n: int, d: f64) -> f64 {
    if i < (n + 1) / 2 {
        i as f64 / (n as f64 * d)
    } else {
        (i - n) as f64 / (n as f64 * d)
    }
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
/* code modified by LLM (iteration 5): Fixed `result.line_get` to `result.nat` for sequence indexing. */
{
    let mut result: Vec<f64> = Vec::new();
    let ghost n_int = n as int;

    let mut i: int = 0;
    while i < n_int
        invariant
            result.len() == i as usize,
            0 <= i <= n_int,
            forall|j: int| 0 <= j < i ==> result.nat(j as nat) == fft_freq_val(j, n_int, d),
        decreases n_int - i
    {
        if i < (n_int + 1) / 2 {
            result.push(i as f64 / (n_int as f64 * d));
        } else {
            result.push((i - n_int) as f64 / (n_int as f64 * d));
        }
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}