// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 2 &&
    (exists|i: int| 0 < i < input.len() && #[trigger] input[i] == ' ') &&
    (forall|i: int| 0 <= i < input.len() ==> (#[trigger] input[i] == ' ' || input[i] == '\n' || ('a' <= input[i] <= 'z'))) &&
    (exists|i: int| 0 < i < input.len() && #[trigger] input[i] == ' ' && 
     (forall|j: int| 0 <= j < i ==> #[trigger] input[j] != ' ' && input[j] != '\n') &&
     (forall|j: int| i+1 <= j < input.len() ==> #[trigger] input[j] != ' ' && input[j] != '\n'))
}

spec fn valid_output(output: Seq<char>) -> bool {
    output.len() > 0 &&
    output[output.len() as int - 1] == '\n' &&
    (forall|i: int| 0 <= i < output.len() - 1 ==> ('a' <= #[trigger] output[i] <= 'z'))
}

spec fn extract_strings(input: Seq<char>) -> (Seq<char>, Seq<char>)
    recommends valid_input(input)
{
    let space_pos = choose|space_pos: int| 0 < space_pos < input.len() && input[space_pos] == ' ' &&
                       (forall|j: int| 0 <= j < space_pos ==> #[trigger] input[j] != ' ') &&
                       (forall|j: int| space_pos+1 <= j < input.len() ==> #[trigger] input[j] != ' ' && input[j] != '\n');
    let s = input.subrange(0, space_pos);
    let t = if input[input.len() as int - 1] == '\n' { 
        input.subrange(space_pos + 1, input.len() - 1) 
    } else { 
        input.subrange(space_pos + 1, input.len() as int) 
    };
    (s, t)
}

spec fn correct_concatenation(input: Seq<char>, output: Seq<char>) -> bool
    recommends valid_input(input)
{
    let (s, t) = extract_strings(input);
    output == t.add(s).push('\n')
}
// </vc-preamble>

// <vc-helpers>
lemma first_space_is_valid(input: Vec<char>, space_pos: int)
    requires
        valid_input(input@),
        0 < space_pos < input.len(),
        input@[space_pos] == ' ',
        forall|j: int| 1 <= j < space_pos ==> input@[j] != ' ',
    ensures
        forall|j: int| 0 <= j < space_pos ==> input@[j] != ' ' && input@[j] != '\n',
        forall|j: int| space_pos+1 <= j < input.len() ==> input@[j] != ' ' && input@[j] != '\n',
{
    let i0 = choose|i0: int| 0 < i0 < input.len() && input@[i0]==' ' &&
             (forall|j: int| 0<=j<i0 ==> input@[j]!=' ' && input@[j]!='\n') &&
             (forall|j: int| i0+1<=j<input.len() ==> input@[j]!=' ' && input@[j]!='\n');
    assert(space_pos == i0);
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires
        valid_input(input@),
    ensures
        valid_output(output@),
        correct_concatenation(input@, output@),
// </vc-spec>
// <vc-code>
{
    let mut space_pos = 0;
    let mut i = 1;
    while i < input.len()
        invariant
            1 <= i <= input.len(),
            forall|j: int| 1 <= j < i ==> input[j] != ' ',
    {
        if input[i] == ' ' {
            space_pos = i;
            break;
        }
        i += 1;
    }
    let s = input[0..space_pos].to_vec();
    let t = input[space_pos+1..].to_vec();
    let mut output = t;
    output.extend(s);
    output.push('\n');
    proof {
        first_space_is_valid(input, space_pos);
        let (spec_s, spec_t) = extract_strings(input@);
        assert(s@ == spec_s && t@ == spec_t);
        assert(valid_output(output@));
    }
    output
}
// </vc-code>


}

fn main() {}