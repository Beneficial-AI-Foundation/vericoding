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
/* helper modified by LLM (iteration 2): remove recommends from proof functions */
proof fn next_char_lemma(c: char)
    ensures ((c as u8) + 1) as char == next_char(c)
{
    assert(((c as u8) + 1) as char == next_char(c));
}

proof fn next_char_range(c: char)
    requires 'a' <= c <= 'y'
    ensures 'b' <= next_char(c) <= 'z'
{
    let next = next_char(c);
    let c_val = c as u8;
    let next_val = c_val + 1;
    assert('a' as u8 == 97);
    assert('y' as u8 == 121);
    assert('b' as u8 == 98);
    assert('z' as u8 == 122);
    assert(97 <= c_val <= 121);
    assert(98 <= next_val <= 122);
    assert(next == next_val as char);
    assert(next_val as char >= 'b');
    assert(next_val as char <= 'z');
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): update to use proof function calls */
{
    let c0 = input[0];
    let c1 = ((c0 as u8) + 1) as char;
    proof {
        next_char_lemma(c0);
        next_char_range(c0);
    }
    let output = vec![c1, '\n'];
    output
}
// </vc-code>


}

fn main() {}