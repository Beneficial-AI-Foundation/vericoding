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
/* helper modified by LLM (iteration 5): prove count_blocks is at least 1 */
proof fn count_blocks_positive(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        count_blocks(n, m) >= 1,
{
    // From valid_input we have 2 <= n and 2 <= m
    assert(2 <= n);
    assert(2 <= m);
    // Therefore (n - 1) >= 1 and (m - 1) >= 1
    assert((n - 1) >= 1);
    assert((m - 1) >= 1);
    // count_blocks is (n-1)*(m-1)
    assert(count_blocks(n, m) == (n - 1) * (m - 1));
    // Product of two integers each >= 1 is >= 1
    assert((n - 1) * (m - 1) >= 1);
}

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
    /* code modified by LLM (iteration 5): compute blocks in int then cast to i8, and prove equality and positivity */
    let ni: int = n as int;
    let mi: int = m as int;
    let blocks_i: int = (ni - 1) * (mi - 1);
    proof {
        // Prove the count_blocks property and positivity
        count_blocks_positive(ni, mi);
        assert(count_blocks(ni, mi) == blocks_i);
        assert(blocks_i >= 1);
    }
    let blocks_i8: i8 = blocks_i as i8;
    proof {
        // Show the returned i8 corresponds to the integer count
        assert((blocks_i8 as int) == blocks_i);
    }
    blocks_i8
}

// </vc-code>


}

fn main() {}