// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && 
    (input[0] == '0' || input[0] == '1') && 
    (input.len() == 1 || (input.len() > 1 && input[1] == '\n'))
}

spec fn logical_not(digit: char) -> Seq<char>
    recommends digit == '0' || digit == '1'
{
    if digit == '0' { seq!['1', '\n'] } else { seq!['0', '\n'] }
}

spec fn correct_output(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    output == logical_not(input[0])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (output: String)
    requires valid_input(input@)
    ensures correct_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed `Seq` indexing issue by converting `input` to a `&Vec<char>` first, allowing direct indexing. */
    let input_vec = input.into_bytes();
    let c = input_vec[0] as char;
    let result_char = if c == '0' { '1' } else { '0' };
    let mut output_string = String::new();
    output_string.push(result_char);
    output_string.push('
');
    output_string
}
// </vc-code>


}

fn main() {}