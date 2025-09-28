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
/* helper modified by LLM (iteration 5): arithmetic proof without nested proof block */
proof fn arith_helper(i: int)
    requires i >= 0
    ensures (i + 1) * i / 2 == i * (i - 1) / 2 + i
{
    assert((i + 1) * i / 2 == (i * i + i) / 2);
    assert(i * (i - 1) / 2 + i == (i * i - i) / 2 + i);
    assert((i * i - i) / 2 + i == (i * i - i + 2 * i) / 2);
    assert((i * i - i + 2 * i) / 2 == (i * i + i) / 2);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow by using larger type and proper arithmetic reasoning */
    let mut sum = 0i32;
    let mut i = 0i32;
    while i < n as i32
        invariant
            0 <= i <= n as i32,
            sum == i * (i - 1) / 2,
        decreases n as i32 - i
    {
        sum = sum + i;
        i = i + 1;
        proof {
            arith_helper((i - 1) as int);
        }
    }
    sum as i8
}
// </vc-code>


}

fn main() {}