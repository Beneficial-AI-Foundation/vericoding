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
/* helper modified by LLM (iteration 2): spec expected_seq returning sequence based on x */
spec fn expected_seq(x: int) -> Seq<char> {
    if x < 1200 {
        seq!['A', 'B', 'C', '\n']
    } else {
        seq!['A', 'R', 'C', '\n']
    }
}

/* helper modified by LLM (iteration 2): runtime expected_vec constructing Vec<char> matching spec */
fn expected_vec(x: i32) -> (res: Vec<char>)
    ensures
        res@ == expected_seq(x as int),
{
    let mut v = Vec::new();
    if x < 1200 {
        v.push('A');
        v.push('B');
        v.push('C');
        v.push('\n');
    } else {
        v.push('A');
        v.push('R');
        v.push('C');
        v.push('\n');
    }
    v
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: Vec<char>)
    requires valid_input(x as int)
    ensures correct_output(x as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use runtime helper expected_vec to build result */
    let result = expected_vec(x);
    result
}
// </vc-code>


}

fn main() {}