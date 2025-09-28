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

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    let mut output = Vec::new();
    let first_char = input[0];
    let next = ((first_char as u8) + 1) as char;
    output.push(next);
    output.push('\n');
    proof {
        assert(output@.len() == 2);
        assert(output@[0] == next_char(input@[0]));
        assert(output@[1] == '\n');
        assert('a' <= input@[0] <= 'y');
        assert(input@[0] as u8 + 1 <= 'y' as u8 + 1);
        assert('b' as u8 <= input@[0] as u8 + 1 <= 'z' as u8);
        assert('b' <= output@[0] <= 'z');
    }
    output
}
// </vc-code>


}

fn main() {}