// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool 
    decreases input.len()
{
    &&& input.len() >= 18
    &&& input[input.len() as int - 1] == '\n'
    &&& input.subrange(0, 7) == seq!['A', 't', 'C', 'o', 'd', 'e', 'r']
    &&& input[7] == ' '
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        #[trigger] input.index(space_pos) == ' ' && 
        input.subrange(space_pos + 1, space_pos + 8) == seq!['C', 'o', 'n', 't', 'e', 's', 't'] &&
        space_pos + 8 == input.len() - 1
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        #[trigger] input.index(space_pos) == ' ' && 
        space_pos > 8 &&
        'A' <= input[8] <= 'Z' &&
        forall|k: int| 9 <= k < space_pos ==> 'a' <= #[trigger] input.index(k) <= 'z'
}

spec fn valid_output(input: Seq<char>, result: Seq<char>) -> bool 
    decreases input.len()
{
    &&& result.len() == 4
    &&& result[0] == 'A'
    &&& result[2] == 'C'
    &&& result[3] == '\n'
    &&& exists|space_pos: int| 8 <= space_pos < input.len() - 8 && 
        #[trigger] input.index(space_pos) == ' ' && 
        result[1] == input[8]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    let space_pos = {
        let mut i = 8;
        while i < input.len() - 8
            invariant
                8 <= i <= input.len() - 8,
                forall|j: int| 8 <= j < i ==> input@[j] != ' ',
            decreases input.len() - i
        {
            if input[i] == ' ' {
                break;
            }
            i += 1;
        }
        i
    };
    
    let initial = input[8];
    let result = vec!['A', initial, 'C', '\n'];
    result
}
// </vc-code>


}

fn main() {}