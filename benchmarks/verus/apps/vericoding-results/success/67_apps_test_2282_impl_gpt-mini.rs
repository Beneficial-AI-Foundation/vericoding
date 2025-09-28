// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<u8>) -> bool {
    input.len() > 0 && exists|i: int| 0 <= i < input.len() && input[i] == 10u8
}

spec fn valid_command_input(input: Seq<u8>) -> bool {
    /* Abstract specification for valid command input */
    input.len() >= 2
}

spec fn extract_n(input: Seq<u8>) -> int {
    /* Abstract specification for extracting n */
    if valid_command_input(input) { 42 } else { 0 }
}

spec fn correct_output(input: Seq<u8>, result: Seq<u8>) -> bool {
    valid_command_input(input) ==> 
        result.len() > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): reflect valid_command_input to concrete length predicate */
proof fn valid_command_input_reflect(input: Vec<u8>)
    ensures
        valid_command_input(input@) == (input.len() >= 2),
{
    // By definition of the spec function valid_command_input, which uses input.len() >= 2
    assert(valid_command_input(input@) == (input.len() >= 2));
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<u8>) -> (result: Vec<u8>)
    requires 
        valid_input(input@),
    ensures 
        correct_output(input@, result@),
        (!valid_command_input(input@) ==> result@.len() == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): produce non-empty result when input.len() >= 2, else empty */
    if input.len() >= 2 {
        let mut result = Vec::<u8>::new();
        result.push(42u8);
        proof {
            valid_command_input_reflect(input);
            assert(input.len() >= 2);
            // From the lemma we conclude the spec predicate holds
            assert(valid_command_input(input@));
            // We pushed an element, so the result sequence is non-empty
            assert(result@.len() > 0);
        }
        result
    } else {
        let result = Vec::<u8>::new();
        proof {
            valid_command_input_reflect(input);
            assert(!(input.len() >= 2));
            assert(!valid_command_input(input@));
            // Result is empty
            assert(result@.len() == 0);
        }
        result
    }
}

// </vc-code>


}

fn main() {}