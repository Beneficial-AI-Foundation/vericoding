// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sum_formula(n: nat) -> (sum: nat)
    ensures
        n == 0 ==> sum == 0,
        n > 0 ==> sum == (n * (n + 1)) / 2,
{
    if n == 0 {
        0
    } else {
        let prev = sum_formula((n - 1) as nat);
        prev + n
    }
}

/* helper modified by LLM (iteration 5): added executable sum function with proper casting */
fn exec_sum(n: u32) -> (sum: u32)
    requires n < 100000,
    ensures
        n == 0 ==> sum == 0,
        n > 0 ==> sum == (n * (n + 1)) / 2,
{
    if n == 0 {
        0
    } else {
        (n * (n + 1)) / 2
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
    /* code modified by LLM (iteration 5): fixed f64 casting by using direct u32 to f64 conversion */
    if n == 0 {
        (0, 0.0)
    } else {
        let sum = exec_sum(n);
        let sum_f64 = sum as f64;
        let n_f64 = n as f64;
        let average = sum_f64 / n_f64;
        (sum, average)
    }
}
// </vc-code>

}
fn main() {}