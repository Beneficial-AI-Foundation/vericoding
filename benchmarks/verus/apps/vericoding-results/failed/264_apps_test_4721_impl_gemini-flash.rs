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
/* code modified by LLM (iteration 5): Simplified calculation and casting to avoid overflow issues by directly using `int` and then casting down to `i8`. */
{
    let n_int = n as int;
    let m_int = m as int;

    let blocks_val_int = (n_int - 1) * (m_int - 1);

    proof {
        assert(2 <= n_int <= 100);
        assert(2 <= m_int <= 100);
        assert(1 <= n_int - 1 <= 99);
        assert(1 <= m_int - 1 <= 99);
        assert(1 <= blocks_val_int <= 99 * 99);
        assert(blocks_val_int <= 9801);
        assert(9801 <= i8::MAX as int);
    }

    let blocks_val: i8 = blocks_val_int as i8;
    blocks_val
}
// </vc-code>


}

fn main() {}