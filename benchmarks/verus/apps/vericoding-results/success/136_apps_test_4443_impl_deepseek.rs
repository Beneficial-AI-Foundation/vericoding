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

proof fn lemma_next_char_in_range(c: char)
    requires 'a' <= c <= 'y'
    ensures 'b' <= next_char(c) <= 'z'
{
    // Proof that incrementing within 'a'-'y' stays in 'b'-'z'
    let c_val = c as int;
    assert('a' as int == 97);
    assert('y' as int == 121);
    assert('b' as int == 98);
    assert('z' as int == 122);
    assert(97 <= c_val <= 121);
    assert(98 <= c_val + 1 <= 122);
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_next_char_in_range(input[0]);
    }
    
    let mut output_vec = Vec::new();
    output_vec.push(((input[0] as u8) + 1) as char);
    output_vec.push('\n');
    
    output_vec
}
// </vc-code>


}

fn main() {}