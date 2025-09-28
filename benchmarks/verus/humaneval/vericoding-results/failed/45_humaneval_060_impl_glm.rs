// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == sum_from_one_to_n(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed invariant block syntax by removing braces and using commas */
{
    let mut i: int = 1;
    let mut s: i8 = 0;

    while i <= n as int
        invariant
            1 <= i <= (n as int) + 1,
            s as int == sum_from_one_to_n(i-1),
        decreases (n as int) - i
    {
        s = s + (i as i8);
        i = i + 1;
    }

    s
}
// </vc-code>


}

fn main() {}