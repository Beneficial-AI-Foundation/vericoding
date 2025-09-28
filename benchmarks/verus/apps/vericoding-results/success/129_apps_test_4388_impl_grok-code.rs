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
proof fn lemma_transform(input: Seq<char>)
    requires
        valid_input(input),
    ensures
        valid_output(input, seq![swap_digit(input[0]), swap_digit(input[1]), swap_digit(input[2]), '\n']),
{
    // assert len
    assert(seq![swap_digit(input[0]), swap_digit(input[1]), swap_digit(input[2]), '\n'].len() == 4);
    // assert last
    assert(seq![swap_digit(input[0]), swap_digit(input[1]), swap_digit(input[2]), '\n'][3] == '\n');
    // assert the property
    assert(forall|i: int| 0 <= i < 3 ==> 
        (input[i] == '1' ==> seq![swap_digit(input[0]), swap_digit(input[1]), swap_digit(input[2]), '\n'][i] == '9') && 
        (input[i] == '9' ==> seq![swap_digit(input[0]), swap_digit(input[1]), swap_digit(input[2]), '\n'][i] == '1')
    );
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    let swapped0 = if input[0] == '1' { '9' } else { '1' };
    let swapped1 = if input[1] == '1' { '9' } else { '1' };
    let swapped2 = if input[2] == '1' { '9' } else { '1' };
    let mut result = Vec::new();
    result.push(swapped0);
    result.push(swapped1);
    result.push(swapped2);
    result.push('\n');
    proof {
        assert(result@ == seq![swapped0, swapped1, swapped2, '\n']);
        assert(swap_digit(input@[0]) == swapped0);
        assert(swap_digit(input@[1]) == swapped1);
        assert(swap_digit(input@[2]) == swapped2);
        lemma_transform(input@);
    }
    result
}
// </vc-code>


}

fn main() {}