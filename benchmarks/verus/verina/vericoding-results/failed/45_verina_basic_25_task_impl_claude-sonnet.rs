// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper function for u32 to f64 conversion */
fn u32_to_f64(x: u32) -> f64
{
    x as f64
}
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
    /* code modified by LLM (iteration 5): use helper function instead of direct cast */
    if n == 0 {
        (0, 0.0)
    } else {
        let sum = (n * (n + 1)) / 2;
        let avg = u32_to_f64(sum) / u32_to_f64(n);
        (sum, avg)
    }
}
// </vc-code>

}
fn main() {}