// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 3 &&
    forall|i: int| 0 <= i < 3 ==> (input[i] == '1' || input[i] == '9')
}

spec fn swap_digit(c: char) -> char {
    if c == '1' { '9' } else { '1' }
}

spec fn transform_string(s: Seq<char>) -> Seq<char> {
    seq![swap_digit(s[0]), swap_digit(s[1]), swap_digit(s[2])]
}

spec fn valid_output(input: Seq<char>, result: Seq<char>) -> bool {
    result.len() == 4 &&
    result[3] == '\n' &&
    forall|i: int| 0 <= i < 3 ==> 
        (input[i] == '1' ==> result[i] == '9') && 
        (input[i] == '9' ==> result[i] == '1')
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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}