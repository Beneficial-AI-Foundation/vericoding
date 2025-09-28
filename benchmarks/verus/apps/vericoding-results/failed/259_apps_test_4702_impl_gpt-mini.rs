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
/* helper modified by LLM (iteration 5): derive non-emptiness of input@ from valid_input */
proof fn input_nonempty(input: String)
    requires
        valid_input(input@),
    ensures
        input@.len() > 0,
{
    assert(valid_input(input@));
    assert(input@.len() > 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (output: String)
    requires valid_input(input@)
    ensures correct_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): branch on first byte and produce logical not */
    let b0 = input.as_bytes()[0];
    if b0 == 48u8 {
        let output = String::from_str("1\n");
        proof {
            assert(valid_input(input@));
            if input@[0] == '0' {
                assert(output@ == logical_not(input@[0]));
            } else {
                assert(output@ == logical_not(input@[0]));
            }
        }
        output
    } else {
        let output = String::from_str("0\n");
        proof {
            assert(valid_input(input@));
            if input@[0] == '1' {
                assert(output@ == logical_not(input@[0]));
            } else {
                assert(output@ == logical_not(input@[0]));
            }
        }
        output
    }
}
// </vc-code>


}

fn main() {}