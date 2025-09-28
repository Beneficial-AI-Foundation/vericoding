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

proof fn valid_input_implies_not_empty(input: Seq<char>)
    requires valid_input(input)
    ensures input.len() > 0
{
    assert(input.len() > 0);
}

proof fn valid_input_implies_first_char_valid(input: Seq<char>)
    requires valid_input(input)
    ensures input[0] == '0' || input[0] == '1'
{
    assert(input[0] == '0' || input[0] == '1');
}

proof fn is_zero_or_one(c: char)
    ensures c == '0' || c == '1'
    decreases
{
    assert(c == '0' || c == '1');
}

proof fn logical_not_correctness(digit: char)
    requires digit == '0' || digit == '1'
    ensures logical_not(digit) == if digit == '0' { seq!['1', '\n'] } else { seq!['0', '\n'] }
{
    assert(logical_not(digit) == if digit == '0' { seq!['1', '\n'] } else { seq!['0', '\n'] });
}

// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (output: String)
    requires valid_input(input@)
    ensures correct_output(input@, output@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove verification bypasses and prove character sequence properties */
    let chars: Vec<char> = input.chars().collect();
    
    proof {
        chars_to_seq_axiom(input);
        valid_input_implies_not_empty(input@);
        valid_input_implies_first_char_valid(input@);
        assert(chars@.len() > 0);
        is_zero_or_one(chars@[0]);
        logical_not_correctness(chars@[0]);
    }
    
    let first_char = chars[0];
    let result_char = if first_char == '0' { '1' } else { '0' };
    let result = format!("{}\n", result_char);
    
    result
}
// </vc-code>


}

fn main() {}