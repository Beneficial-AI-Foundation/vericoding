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
proof fn lemma_valid_command_input_len_equiv(s: Seq<u8>)
    ensures
        valid_command_input(s) == (s.len() >= 2),
{
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
    let mut result: Vec<u8> = Vec::new();
    if input.len() >= 2 {
        proof { assert(valid_command_input(input@)); }
        result.push(42u8);
    } else {
        proof { assert(!valid_command_input(input@)); }
    }
    result
}
// </vc-code>


}

fn main() {}