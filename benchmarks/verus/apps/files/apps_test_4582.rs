// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 3 &&
    input[1] == ' ' &&
    (input[0] == 'H' || input[0] == 'D') &&
    (input[2] == 'H' || input[2] == 'D') &&
    (input.len() == 3 || (input.len() > 3 && input[3] == '\n'))
}

spec fn correct_output(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    if (input[0] == 'H' && input[2] == 'H') || (input[0] == 'D' && input[2] == 'D') {
        seq!['H', '\n']
    } else {
        seq!['D', '\n']
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures result == correct_output(input)
    ensures (result == seq!['H', '\n']) || (result == seq!['D', '\n'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}