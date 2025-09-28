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
proof fn lemma_multiplication_properties(n: int, m: int)
    requires
        valid_input(n, m)
    ensures
        (n - 1) >= 0,
        (m - 1) >= 0,
        (n - 1) <= 99,
        (m - 1) <= 99,
        ((n - 1) * (m - 1)) >= 0,
        ((n - 1) * (m - 1)) <= 9801
{
    assert(2 <= n <= 100);
    assert(2 <= m <= 100);
    assert(n - 1 >= 1);
    assert(m - 1 >= 1);
    assert(n - 1 <= 99);
    assert(m - 1 <= 99);
    assert((n - 1) * (m - 1) >= 1 * 1);
    assert((n - 1) * (m - 1) <= 99 * 99);
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
    /* code modified by LLM (iteration 5): Fixed casting with proper bounds and removed invalid is i8 syntax */
    proof {
        lemma_count_blocks_formula(n as int, m as int);
        lemma_multiplication_properties(n as int, m as int);
    }
    
    let n1 = (n - 1) as i8;
    let m1 = (m - 1) as i8;
    let result = n1 * m1;
    
    result
}
// </vc-code>


}

fn main() {}