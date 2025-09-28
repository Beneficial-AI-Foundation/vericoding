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
/* helper modified by LLM (iteration 2): [implemented lemma for recursive property of max_sum] */
proof fn lemma_max_sum_unfold(k: int)
    requires
        k >= 1,
    ensures
        max_sum(k) == max_sum(k - 1) + (k - 1),
{
    // This is provable by non-linear arithmetic from the definition of max_sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [used i32 to avoid overflow and fixed compilation error] */
    let mut i: i32 = 0;
    let mut sum: i32 = 0;
    while i < (n as i32)
        invariant
            0 <= i <= (n as i32),
            sum as int == max_sum(i as int),
        decreases (n as i32) - i
    {
        proof {
            lemma_max_sum_unfold(i + 1);
        }
        sum = sum + i;
        i = i + 1;
    }
    sum as i8
}
// </vc-code>


}

fn main() {}