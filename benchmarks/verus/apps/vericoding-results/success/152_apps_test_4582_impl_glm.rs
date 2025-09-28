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
{
    let first_char = input[0];
    let third_char = input[2];
    
    if (first_char == 'H' && third_char == 'H') || (first_char == 'D' && third_char == 'D') {
        vec!['H', '\n']
    } else {
        vec!['D', '\n']
    }
}
// </vc-code>


}

fn main() {}