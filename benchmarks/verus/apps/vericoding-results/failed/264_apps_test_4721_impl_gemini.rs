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
/* helper modified by LLM (iteration 2): add asserts to help prove positivity */
proof fn lemma_count_blocks_is_positive(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        count_blocks(n, m) >= 1,
{
    assert(n - 1 >= 1);
    assert(m - 1 >= 1);
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
    /* code modified by LLM (iteration 2): fixed overflow by using a wider intermediate type */
    let blocks_i16 = (n as i16 - 1) * (m as i16 - 1);
    blocks_i16 as i8
}
// </vc-code>


}

fn main() {}