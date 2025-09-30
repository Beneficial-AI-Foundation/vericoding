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
fn build_result(ch: char) -> (result: Vec<char>)
    ensures
        result@ == seq!['A', ch, 'C', '\n'],
{
    let mut v = Vec::new();
    v.push('A');
    v.push(ch);
    v.push('C');
    v.push('\n');
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    let idx: usize = 8usize;
    assert(input.len() >= 18usize);
    assert(idx < input.len());
    let ch = input[idx];
    let result = build_result(ch);
    result
}
// </vc-code>


}

fn main() {}