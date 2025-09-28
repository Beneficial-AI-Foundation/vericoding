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
/* helper modified by LLM (iteration 5): use chars().nth(0) instead of iterator next() */
fn get_first_char(s: &str) -> (result: char)
    requires
        s@.len() > 0,
    ensures
        result == s@[0],
{
    proof {
        assert(s@.len() > 0);
    }
    let first = s.chars().nth(0);
    first.unwrap()
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (output: String)
    requires valid_input(input@)
    ensures correct_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): access string chars directly without helper */
    let first_char = input.chars().nth(0).unwrap();
    if first_char == '0' {
        "1\n".to_string()
    } else {
        "0\n".to_string()
    }
}
// </vc-code>


}

fn main() {}