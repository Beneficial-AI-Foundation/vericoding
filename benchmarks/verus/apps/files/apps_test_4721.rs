// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    2 <= n <= 100 && 2 <= m <= 100
}

spec fn count_blocks(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    (n - 1) * (m - 1)
}

spec fn correct_output(n: int, m: int, blocks: int) -> bool {
    valid_input(n, m) && blocks == count_blocks(n, m)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (blocks: i8)
    requires 
        valid_input(n as int, m as int)
    ensures 
        correct_output(n as int, m as int, blocks as int),
        blocks >= 1
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}