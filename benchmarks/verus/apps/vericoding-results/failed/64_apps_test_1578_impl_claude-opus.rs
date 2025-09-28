// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_sum(n: int) -> int
    recommends n >= 1
{
    n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant formula for sum */
    let mut sum: i32 = 0;
    let mut i: i8 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == (i as i32 - 1) * (i as i32 - 2) / 2,
            valid_input(n as int),
            sum >= 0,
            sum <= 127,
        decreases (n - i + 1) as int
    {
        if i < n {
            sum = sum + (i as i32);
        }
        i = i + 1;
    }
    
    proof {
        assert(i == n + 1);
        assert(sum == n as i32 * (n as i32 - 1) / 2);
    }
    
    sum as i8
}
// </vc-code>


}

fn main() {}