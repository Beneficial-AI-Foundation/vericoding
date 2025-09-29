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
/* helper modified by LLM (iteration 4): relate Vec index to Seq index for char */
proof fn vec_index_seq_eq_char(v: Vec<char>, i: int)
    requires 0 <= i < v.len(),
    ensures v@[i] == v[i],
{
    // The Seq view of a Vec agrees with runtime indexing at index i
    assert(v@[i] == v[i]);
}

/* helper modified by LLM (iteration 4): runtime conditional equals spec swap_digit */
proof fn swap_char_correct(v: Vec<char>, i: int)
    requires valid_input(v@), 0 <= i < 3,
    ensures (if v[i] == '1' { '9' } else { '1' }) == swap_digit(v@[i]),
{
    vec_index_seq_eq_char(v, i);
    if v[i] == '1' {
        assert(v@[i] == '1');
        assert(swap_digit(v@[i]) == '9');
    } else {
        assert(v[i] != '1');
        assert(v@[i] != '1');
        // From valid_input(v@) we know v@[i] is either '1' or '9', combined with v@[i] != '1' gives '9'
        assert(v@[i] == '9');
        assert(swap_digit(v@[i]) == '1');
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(input@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build result Vec and prove valid_output */
    let mut result = Vec::<char>::new();
    let c0 = if input[0] == '1' { '9' } else { '1' };
    let c1 = if input[1] == '1' { '9' } else { '1' };
    let c2 = if input[2] == '1' { '9' } else { '1' };
    result.push(c0);
    result.push(c1);
    result.push(c2);
    result.push('\n');

    proof {
        swap_char_correct(input, 0);
        swap_char_correct(input, 1);
        swap_char_correct(input, 2);
        assert(result@ == seq![swap_digit(input@[0]), swap_digit(input@[1]), swap_digit(input@[2]), '\n']);
        assert(valid_output(input@, result@));
    }

    result
}

// </vc-code>


}

fn main() {}