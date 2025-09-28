// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    1 <= x <= 3000
}

spec fn correct_output(x: int, result: Seq<char>) -> bool {
    (x < 1200 ==> result == seq!['A', 'B', 'C', '\n']) &&
    (x >= 1200 ==> result == seq!['A', 'R', 'C', '\n'])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: Vec<char>)
    requires valid_input(x as int)
    ensures correct_output(x as int, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}