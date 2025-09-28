// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: u32) -> (result: (u32, f64))
    requires n < 100000,
    ensures
        n == 0 ==> result.0 == 0,
        n > 0 ==> result.0 == (n * (n + 1)) / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed unsupported cast from i64 to f64 by casting u32 to f64 directly */
    if n == 0 {
        (0, 0.0)
    } else {
        let n_i64 = n as i64;
        let sum_i64 = (n_i64 * (n_i64 + 1)) / 2;
        let sum_u32 = sum_i64 as u32;
        let n_f = n as f64;
        let avg = (n_f + 1.0) / 2.0;
        (sum_u32, avg)
    }
}
// </vc-code>

}
fn main() {}