// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 'a' <= input[0] <= 'y'
}

spec fn next_char(c: char) -> char
    recommends 'a' <= c <= 'y'
{
    ((c as u8) + 1) as char
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    output.len() == 2 &&
    output[0] == next_char(input[0]) &&
    output[1] == '\n' &&
    'b' <= output[0] <= 'z'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper is correct as is and necessary for the proof */
proof fn lemma_next_char_in_range(c: char)
    requires
        'a' <= c <= 'y',
    ensures
        'b' <= next_char(c) <= 'z',
{}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): wrapped lemma call in a proof block to fix compilation error */
    proof {
        lemma_next_char_in_range(input[0]);
    }
    let next_c = ((input[0] as u8) + 1) as char;
    let output = vec![next_c, '\n'];
    output
}
// </vc-code>


}

fn main() {}