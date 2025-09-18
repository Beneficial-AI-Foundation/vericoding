// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes */
spec fn nanvar_spec(a: Seq<f32>, ddof: nat) -> f32 {
    if a.len() == 0 || (ddof as int) >= a.len() {
        0.0 // Or some other appropriate value for invalid input
    } else {
        let sum_val: f32 = a.fold(0.0, |acc: f32, x: f32| acc + x);
        let avg_val: f32 = sum_val / (a.len() as f32);
        let sq_diff_sum: f32 = a.fold(0.0, |acc: f32, x: f32| acc + (x - avg_val) * (x - avg_val));
        sq_diff_sum / ((a.len() as int - ddof as int) as f32)
    }
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed extraneous indentation from invariants */
{
    let n = a.len();
    if n == 0 || ddof >= n {
        return 0.0f32;
    }

    let mut sum: f32 = 0.0f32;
    let mut i: usize = 0;
    while i < n
        invariant n == a.len(),
        invariant i <= n,
        invariant
            sum == a.subsequence(0, i as int).fold(0.0, |acc: f32, x: f32| acc + x)
    {
        sum = sum + a@[i];
        i = i + 1;
    }
    let avg: f32 = sum / (n as f32);

    let mut sq_diff_sum: f32 = 0.0f32;
    let mut i: usize = 0;
    while i < n
        invariant n == a.len(),
        invariant i <= n,
        invariant
            sq_diff_sum == a.subsequence(0, i as int).fold(0.0, |acc: f32, x: f32| acc + (x - avg) * (x - avg))
    {
        let diff = a@[i] - avg;
        sq_diff_sum = sq_diff_sum + diff * diff;
        i = i + 1;
    }

    let divisor = (n - ddof) as f32;
    sq_diff_sum / divisor
}
// </vc-code>

}
fn main() {}