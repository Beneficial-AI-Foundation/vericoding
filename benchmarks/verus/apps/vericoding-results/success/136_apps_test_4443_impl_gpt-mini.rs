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
/* helper modified by LLM (iteration 4): prove next_char produces a char in ['b','z'] */
proof fn next_char_range(c: char)
    requires
        'a' <= c <= 'y',
    ensures
        'b' <= next_char(c) <= 'z',
{
    let nc = next_char(c);
    assert(nc == (((c as u8) + 1) as char));
    assert('b' <= nc);
    assert(nc <= 'z');
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): construct output of length 2 with next char and newline */
    let mut output: Vec<char> = Vec::new();
    let c: char = input[0];
    let nc: char = (((c as u8) + 1) as char);
    output.push(nc);
    output.push('\n');
    output
}

// </vc-code>


}

fn main() {}