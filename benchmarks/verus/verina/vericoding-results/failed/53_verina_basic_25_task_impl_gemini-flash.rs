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
/* code modified by LLM (iteration 5): fixed cast error by using n.nat() to convert to nat first, then as f64 */
{
    let sum: u32 = (n * (n + 1)) / 2;
    let average: f64;

    if n == 0 {
        average = 0.0;
    }
    else {
        let n_f64: f64 = n.nat() as f64;
        average = sum as f64 / n_f64;
    }

    (sum, average)
}
// </vc-code>

}
fn main() {}