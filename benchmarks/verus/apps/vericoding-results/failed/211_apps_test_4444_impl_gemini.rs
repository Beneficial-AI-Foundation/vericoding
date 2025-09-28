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
/* helper modified by LLM (iteration 4): fixed forall syntax error */
spec fn is_all_letters(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('a' <= s[i] && s[i] <= 'z')
}

/* helper modified by LLM (iteration 4): fixed forall syntax error */
#[verifier::spinoff_prover]
proof fn lemma_characterize_split(input: Seq<char>, space_pos: int)
    requires
        valid_input(input),
        1 <= space_pos < input.len(),
        input[space_pos] == ' ',
        forall|j: int| 0 <= j < space_pos ==> input[j] != ' ' && input[j] != '\n',
    ensures
        extract_strings(input).0 == input.subrange(0, space_pos),
        is_all_letters(extract_strings(input).0),
        is_all_letters(extract_strings(input).1),
{
    let spec_space_pos = choose|i: int| 0 < i < input.len() && input[i] == ' ' &&
                           (forall|j: int| 0 <= j < i ==> #[trigger] input[j] != ' ' && input[j] != '\n') &&
                           (forall|j: int| i+1 <= j < input.len() ==> #[trigger] input[j] != ' ' && input[j] != '\n');
    assert(space_pos == spec_space_pos);

    let (s, t) = extract_strings(input);
    assert(s == input.subrange(0, space_pos));

    forall|i: int| 0 <= i < s.len()
    ensures 'a' <= s[i] && s[i] <= 'z'
    {
        let j = i;
        assert(input@[j] != ' ' && input@[j] != '\n');
        assert(valid_input(input));
        assert(input@[j] == ' ' || input@[j] == '\n' || ('a' <= input@[j] && input@[j] <= 'z'));
        assert('a' <= input@[j] && input@[j] <= 'z');
        assert(s@[i] == input@[j]);
    }
    assert(is_all_letters(s));

    let end_of_t_idx = if input[input.len() as int - 1] == '\n' { input.len() as int - 1 } else { input.len() as int };
    forall|i: int| 0 <= i < t.len()
    ensures 'a' <= t[i] && t[i] <= 'z'
    {
        let j = spec_space_pos + 1 + i;
        assert(spec_space_pos + 1 <= j < end_of_t_idx);
        assert(input@[j] != ' ' && input@[j] != '\n');
        assert(valid_input(input));
        assert(input@[j] == ' ' || input@[j] == '\n' || ('a' <= input@[j] && input@[j] <= 'z'));
        assert('a' <= input@[j] && input@[j] <= 'z');
        assert(t@[i] == input@[j]);
    }
    assert(is_all_letters(t));
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
    /* code modified by LLM (iteration 4): no changes, passing through */
    let mut space_pos: usize = 1;
    while space_pos < input.len()
        invariant
            1 <= space_pos <= input.len(),
            valid_input(input@),
            forall|j: int| 0 <= j < space_pos as int ==> input@[j] != ' ' && input@[j] != '\n',
        decreases input.len() - space_pos
    {
        if input[space_pos] == ' ' {
            break;
        }
        space_pos = space_pos + 1;
    }

    lemma_characterize_split(input@, space_pos as int);

    let (s, t) = extract_strings(input@);
    
    let end_of_t = if input[input.len() - 1] == '\n' {
        (input.len() - 1) as usize
    } else {
        input.len() as usize
    };
    assert(t == input@.subrange(space_pos as int + 1, end_of_t as int));

    let mut output: Vec<char> = Vec::new();
    
    let mut i: usize = space_pos + 1;
    while i < end_of_t
        invariant
            space_pos + 1 <= i <= end_of_t,
            output@ == input@.subrange(space_pos as int + 1, i as int),
        decreases end_of_t - i
    {
        output.push(input[i]);
        i = i + 1;
    }
    assert(output@ == t);
    
    let mut j: usize = 0;
    while j < space_pos
        invariant
            0 <= j <= space_pos,
            output@ == t.add(input@.subrange(0, j as int)),
        decreases space_pos - j
    {
        output.push(input[j]);
        j = j + 1;
    }
    assert(output@ == t.add(s));
    
    output.push('\n');
    
    output
}
// </vc-code>


}

fn main() {}