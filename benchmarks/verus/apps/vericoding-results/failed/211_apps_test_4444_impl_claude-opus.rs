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
    /* code modified by LLM (iteration 5): simplified invariants to fix trigger inference issues */
    let mut i: usize = 0;
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            valid_input(input@),
        decreases input.len() - i
    {
        if input[i] == ' ' {
            break;
        }
        i = i + 1;
    }
    
    let space_pos = i;
    assert(0 < space_pos < input.len());
    assert(input@[space_pos as int] == ' ');
    
    let mut j: usize = space_pos + 1;
    let mut output: Vec<char> = Vec::new();
    
    while j < input.len()
        invariant
            space_pos + 1 <= j <= input.len(),
            valid_input(input@),
            0 < space_pos < input.len(),
            input@[space_pos as int] == ' ',
            output.len() == j - (space_pos + 1),
            forall|k: int| 0 <= k < output.len() ==> #[trigger] output@[k] == input@[space_pos as int + 1 + k],
        decreases input.len() - j
    {
        if input[j] != '\n' {
            output.push(input[j]);
        }
        j = j + 1;
    }
    
    let t_len = if input@[input.len() - 1] == '\n' { input.len() - space_pos - 2 } else { input.len() - space_pos - 1 };
    let mut k: usize = 0;
    while k < space_pos
        invariant
            0 <= k <= space_pos,
            valid_input(input@),
            0 < space_pos < input.len(),
            input@[space_pos as int] == ' ',
            output.len() == t_len + k,
            forall|m: int| 0 <= m < t_len ==> #[trigger] output@[m] == input@[space_pos as int + 1 + m],
            forall|m: int| 0 <= m < k ==> #[trigger] output@[t_len + m] == input@[m],
        decreases space_pos - k
    {
        output.push(input[k]);
        k = k + 1;
    }
    
    output.push('\n');
    
    proof {
        let (s, t) = extract_strings(input@);
        assert(s == input@.subrange(0, space_pos as int));
        assert(t == if input@[input.len() - 1] == '\n' { 
            input@.subrange(space_pos as int + 1, input.len() - 1) 
        } else { 
            input@.subrange(space_pos as int + 1, input.len() as int) 
        });
        assert(output@ == t.add(s).push('\n'));
    }
    
    output
}
// </vc-code>


}

fn main() {}