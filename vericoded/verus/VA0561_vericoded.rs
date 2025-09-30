// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 1998
}

spec fn expected_result(n: int) -> Seq<char> {
    if n < 1000 { seq!['A', 'B', 'C'] } else { seq!['A', 'B', 'D'] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): lemma about valid_input bounds, not strictly needed but kept for clarity */
proof fn lemma_valid_input_bounds(n: int)
    requires
        valid_input(n),
    ensures
        1 <= n,
        n <= 1998,
{
    assert(valid_input(n) == (1 <= n <= 1998));
    assert(1 <= n <= 1998);
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i32) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == expected_result(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): construct Vec by pushes matching expected_result without ghost args */
    let mut v: Vec<char> = Vec::new();
    v.push('A');
    v.push('B');
    if n < 1000 {
        v.push('C');
    } else {
        v.push('D');
    }
    v
}
// </vc-code>


}

fn main() {}