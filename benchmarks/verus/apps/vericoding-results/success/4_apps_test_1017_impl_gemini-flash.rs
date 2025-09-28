// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_distributions(n: int) -> int
    recommends valid_input(n)
{
    if n % 3 == 0 { 2 * (n / 3) } else { 2 * (n / 3) + 1 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result >= 1,
        result as int == max_distributions(n as int)
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 4): Fix compilation error: use of `int` in exec code is not allowed. */
    let n_i8: i8 = n;
    let result_i8: i8;

    if n_i8 % 3 == 0 {
        result_i8 = 2 * (n_i8 / 3);
    } else {
        result_i8 = 2 * (n_i8 / 3) + 1;
    }
    
    // Proof to show that the result_i8 is equal to the spec function's result
    proof {
        let n_int: int = n as int;
        let result_int = if n_int % 3 == 0 {
            2 * (n_int / 3)
        } else {
            2 * (n_int / 3) + 1
        };
        assert(result_i8 as int == result_int);
    }
    result_i8
}
// </vc-code>


}

fn main() {}