// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(input: Seq<char>) -> bool {
    &&& input.len() >= 18
    &&& input[input.len() - 1] == '\n'
    &&& input.subrange(0, 7) == seq!['A', 't', 'C', 'o', 'd', 'e', 'r']
    &&& input[7] == ' '
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        input[space_pos] == ' ' && 
        input.subrange(space_pos + 1, space_pos + 8) == seq!['C', 'o', 'n', 't', 'e', 's', 't'] &&
        space_pos + 8 == input.len() - 1
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        input[space_pos] == ' ' && 
        space_pos > 8 &&
        'A' <= input[8] <= 'Z' &&
        forall|k: int| 9 <= k < space_pos ==> 'a' <= input[k] <= 'z'
}

spec fn valid_output(input: Seq<char>, result: Seq<char>) -> bool {
    &&& result.len() == 4
    &&& result[0] == 'A'
    &&& result[2] == 'C'
    &&& result[3] == '\n'
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        input[space_pos] == ' ' && 
        result[1] == input[8]
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures valid_output(input, result)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}