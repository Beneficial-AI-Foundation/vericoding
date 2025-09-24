// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: &str) -> bool {
    true
}

spec fn min_lanterns(n: int, m: int) -> int {
    if n >= 1 && m >= 1 {
        (n * m + 1) / 2
    } else {
        0
    }
}

spec fn valid_output(input: &str, output: Seq<int>) -> bool {
    true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_lanterns() -> (result: bool)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}