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
    /* code modified by LLM (iteration 5): use proof blocks for int conversions and proper spec calculations */
    
    if n == 0 {
        (0, 0.0)
    } else {
        let sum = (n * (n + 1)) / 2;
        
        proof {
            let sum_int: int = sum as int;
            let n_int: int = n as int;
        }
        
        let avg = (sum as f64) / (n as f64);
        (sum, avg)
    }
}
// </vc-code>

}
fn main() {}