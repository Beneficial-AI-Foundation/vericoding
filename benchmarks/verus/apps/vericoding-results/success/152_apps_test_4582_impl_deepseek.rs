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

proof fn lemma_input_len(input: Seq<char>)
    requires valid_input(input)
    ensures input.len() >= 3,
{
}

proof fn lemma_input_chars(input: Seq<char>)
    requires valid_input(input)
    ensures input[1] == ' ',
            (input[0] == 'H' || input[0] == 'D'),
            (input[2] == 'H' || input[2] == 'D'),
            (input.len() == 3 || (input.len() > 3 && input[3] == '\n')),
{
}

spec fn first_char(input: Seq<char>) -> char {
    input[0]
}

spec fn third_char(input: Seq<char>) -> char {
    input[2]
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == correct_output(input@)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_input_len(input@);
        lemma_input_chars(input@);
    }
    
    let first = input[0];
    let third = input[2];
    let result_char = if (first == 'H' && third == 'H') || (first == 'D' && third == 'D') {
        'H'
    } else {
        'D'
    };
    
    vec![result_char, '\n']
}
// </vc-code>


}

fn main() {}