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
    /* code modified by LLM (iteration 5): Fixed compilation errors by casting `input.len()` to `nat` for Vec indexing and subrange bounds. */
    let mut space_idx: nat = 0; // Changed to nat
    while (space_idx as int) < input.len()
        invariant
            space_idx <= input.len(),
            (forall|j: int| 0 <= j < space_idx ==> #[trigger] input@[j] != ' ' && input@[j] != '\n'),
        decreases input.len() - (space_idx as int),
    {
        if input@[space_idx] == ' ' {
            break;
        }
        space_idx = (space_idx + 1) as nat;
    }

    let s_seq = input@.subrange(0, space_idx as int);
    let mut t_seq: Seq<char>;

    if input.len() > 0 && input@[ (input.len() - 1) as nat] == '\n' { // Cast input.len() - 1 to nat
        t_seq = input@.subrange((space_idx + 1) as int, (input.len() - 1) as int);
    } else {
        t_seq = input@.subrange((space_idx + 1) as int, input.len() as int);
    }

    proof {
        assert(extract_strings(input@).1.add(extract_strings(input@).0).push('\n') =~= t_seq.add(s_seq).push('\n'));
    }

    let result_seq = t_seq.add(s_seq).push('\n');

    let mut result_vec = Vec::new();
    let mut i: nat = 0; // Changed to nat
    while (i as int) < result_seq.len()
        invariant
            i <= result_seq.len(),
            result_vec@ == result_seq.subrange(0, i as int),
        decreases result_seq.len() - (i as int)
    {
        result_vec.push(result_seq.index(i as int));
        i = (i + 1) as nat;
    }

    result_vec
}
// </vc-code>


}

fn main() {}