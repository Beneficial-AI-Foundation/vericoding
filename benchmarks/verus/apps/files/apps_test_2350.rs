// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_test_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

spec fn count_different_sums(x1: int, y1: int, x2: int, y2: int) -> int
    recommends valid_test_case(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures output@.len() >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}