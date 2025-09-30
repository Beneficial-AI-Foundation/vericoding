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
/* helper modified by LLM (iteration 2): no helpers required */
// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: Vec<char>)
    requires valid_input(x as int)
    ensures correct_output(x as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix newline char literal and assertions */
    let mut v: Vec<char> = Vec::new();
    v.push('A');
    if x < 1200 {
        v.push('B');
    } else {
        v.push('R');
    }
    v.push('C');
    v.push('\n');
    if x < 1200 {
        assert(v@ == seq!['A', 'B', 'C', '\n']);
    } else {
        assert(v@ == seq!['A', 'R', 'C', '\n']);
    }
    v
}
// </vc-code>


}

fn main() {}