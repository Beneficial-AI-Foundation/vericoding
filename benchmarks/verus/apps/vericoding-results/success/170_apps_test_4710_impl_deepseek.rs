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
proof fn lemma_correct_output_holds(x: int)
    requires valid_input(x),
    ensures correct_output(x, (if x < 1200 { seq!['A', 'B', 'C', '\n'] } else { seq!['A', 'R', 'C', '\n'] }))
{
    /* helper modified by LLM (iteration 5): Fixed proof to satisfy postcondition */
    if x < 1200 {
        assert(correct_output(x, seq!['A', 'B', 'C', '\n']));
    } else {
        assert(correct_output(x, seq!['A', 'R', 'C', '\n']));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i32) -> (result: Vec<char>)
    requires valid_input(x as int)
    ensures correct_output(x as int, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation with proper proof */
    let mut result = Vec::new();
    result.push('A');
    
    if x < 1200 {
        result.push('B');
    } else {
        result.push('R');
    }
    
    result.push('C');
    result.push('\n');
    
    proof {
        lemma_correct_output_holds(x as int);
        assert(result@ == (if x < 1200 { seq!['A', 'B', 'C', '\n'] } else { seq!['A', 'R', 'C', '\n'] }));
    }
    
    result
}
// </vc-code>


}

fn main() {}