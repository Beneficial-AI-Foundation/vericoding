// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 3 &&
    input[1] == ' ' &&
    (input[0] == 'H' || input[0] == 'D') &&
    (input[2] == 'H' || input[2] == 'D') &&
    (input.len() == 3 || (input.len() > 3 && input[3] == '\n'))
}

spec fn correct_output(input: Seq<char>) -> Seq<char> {
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D') {
        seq!['H', '\n']
    } else {
        seq!['D', '\n']
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == correct_output(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Access vector elements without @ for runtime operations. */
{
    let output: Vec<char>;
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D') {
        output = vec!['H', '\n'];
    } else {
        output = vec!['D', '\n'];
    }
    output
}
// </vc-code>


}

fn main() {}