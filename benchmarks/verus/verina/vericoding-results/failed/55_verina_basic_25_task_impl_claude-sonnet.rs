// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn sum_first_n(n: u32) -> u32
    requires n < 100000
    ensures n == 0 ==> result == 0,
            n > 0 ==> result == (n * (n + 1)) / 2
{
    if n == 0 {
        0
    } else {
        n * (n + 1) / 2
    }
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
    let sum = sum_first_n(n);
    let avg = if n == 0 { 0.0 } else { sum as f64 / n as f64 };
    (sum, avg)
}
// </vc-code>

}
fn main() {}