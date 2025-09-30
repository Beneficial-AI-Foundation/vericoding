// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    (stdin_input[stdin_input.len() as int - 1] == '\n' || 
     !exists|i: int| 0 <= i < stdin_input.len() && stdin_input[i] == '\n')
}

spec fn valid_result(result: Seq<char>) -> bool {
    result == seq!['B','i','t','A','r','y','o'] || result == seq!['B','i','t','L','G','M']
}

spec fn game_result(stdin_input: Seq<char>) -> Seq<char>
    recommends valid_input(stdin_input)
{
    seq!['B','i','t','L','G','M']
}
// </vc-preamble>

// <vc-helpers>
fn build_bitlgm() -> (v: Vec<char>)
    ensures
        v@ == seq!['B','i','t','L','G','M'],
{
    let mut v: Vec<char> = Vec::new();
    v.push('B');
    v.push('i');
    v.push('t');
    v.push('L');
    v.push('G');
    v.push('M');
    proof {
        assert(v@ == seq!['B','i','t','L','G','M']);
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(stdin_input@)
    ensures valid_result(result@)
// </vc-spec>
// <vc-code>
{
    let result = build_bitlgm();
    proof {
        assert(valid_result(result@));
    }
    result
}
// </vc-code>


}

fn main() {}