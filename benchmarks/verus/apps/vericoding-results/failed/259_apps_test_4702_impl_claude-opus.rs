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
    /* code modified by LLM (iteration 5): Fixed type errors by using proper nat literal and sequence indexing syntax */
    let output = if input@.len() > 0nat && input@[0int] == '0' {
        String::from_str("1\n")
    } else {
        String::from_str("0\n")
    };
    
    proof {
        assert(valid_input(input@));
        assert(input@.len() > 0);
        assert(input@[0] == '0' || input@[0] == '1');
        
        if input@[0] == '0' {
            assert(output@ == seq!['1', '\n']);
            assert(logical_not(input@[0]) == seq!['1', '\n']);
        } else {
            assert(input@[0] == '1');
            assert(output@ == seq!['0', '\n']);
            assert(logical_not(input@[0]) == seq!['0', '\n']);
        }
        assert(output@ == logical_not(input@[0]));
        assert(correct_output(input@, output@));
    }
    
    output
}
// </vc-code>


}

fn main() {}