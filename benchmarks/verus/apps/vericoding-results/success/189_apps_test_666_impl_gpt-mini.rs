// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn triangular_number(m: int) -> int
    recommends m >= 0
{
    m * (m + 1) / 2
}

spec fn valid_input(n: int) -> bool
{
    n >= 1
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result >= 1 && result <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): trivial lemma that 1 <= n from n >= 1 */
proof fn lemma_one_le_n(n: int)
    requires
        n >= 1,
    ensures
        1 <= n,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): return n directly to satisfy bounds */
    let result: i8 = n;
    result
}
// </vc-code>


}

fn main() {}