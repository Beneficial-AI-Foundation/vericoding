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
/* helper modified by LLM (iteration 3): Fixed character escaping for newlines */
fn lemma_extract_strings_properties(input: Seq<char>)
    requires valid_input(input)
    ensures
        let (s, t) = extract_strings(input),
        s.len() > 0,
        t.len() > 0,
        (forall|i: int| 0 <= i < s.len() ==> ('a' <= s[i] <= 'z')),
        (forall|i: int| 0 <= i < t.len() ==> ('a' <= t[i] <= 'z'))
{
}

fn lemma_find_space_unique(input: Seq<char>) -> (space_pos: usize)
    requires valid_input(input)
    ensures
        0 < space_pos < input.len(),
        input[space_pos as int] == ' ',
        (forall|j: int| 0 <= j < space_pos ==> input[j] != ' ' && input[j] != '\n'),
        (forall|j: int| space_pos + 1 <= j < input.len() ==> input[j] != ' ' && input[j] != '\n')
{
    let mut i = 1;
    while i < input.len()
        invariant
            1 <= i <= input.len(),
            (forall|j: int| 0 <= j < i ==> input[j] != ' ')
    {
        if input[i as int] == ' ' {
            return i;
        }
        i += 1;
    }
    unreached()
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
    /* code modified by LLM (iteration 3): Fixed newline escaping and variable declaration */
    let mut space_pos: usize = 1;
    while space_pos < input.len()
        invariant
            1 <= space_pos <= input.len(),
            (forall|j: int| 0 <= j < space_pos ==> input@[j] != ' ')
    {
        if input[space_pos] == ' ' {
            break;
        }
        space_pos += 1;
    }
    
    let s_len = space_pos;
    let t_start = space_pos + 1;
    let t_len = if input[input.len() - 1] == '\n' {
        input.len() - 1 - t_start
    } else {
        input.len() - t_start
    };
    
    let mut output = Vec::with_capacity(s_len + t_len + 1);
    
    // Add t first
    let mut i = 0;
    while i < t_len
        invariant
            0 <= i <= t_len,
            output.len() == i,
            (forall|j: int| 0 <= j < i ==> output@[j] == input@[t_start + j])
    {
        output.push(input[t_start + i]);
        i += 1;
    }
    
    // Add s second
    i = 0;
    while i < s_len
        invariant
            0 <= i <= s_len,
            output.len() == t_len + i,
            (forall|j: int| 0 <= j < t_len ==> output@[j] == input@[t_start + j]),
            (forall|j: int| 0 <= j < i ==> output@[t_len + j] == input@[j])
    {
        output.push(input[i]);
        i += 1;
    }
    
    // Add newline
    output.push('\n');
    
    proof {
        lemma_extract_strings_properties(input@);
    }
    
    output
}
// </vc-code>


}

fn main() {}