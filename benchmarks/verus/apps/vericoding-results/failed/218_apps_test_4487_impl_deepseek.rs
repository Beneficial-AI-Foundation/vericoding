// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_parsed_input(parts: Seq<Seq<char>>) -> bool {
    parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0
}

spec fn is_word_chain(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    a.len() > 0 && b.len() > 0 && c.len() > 0 &&
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}

spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

spec fn expected_result(input: Seq<char>) -> Seq<char> {
    let stripped = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input.subrange(0, input.len() - 1)
    } else {
        input
    };
    let parts = split_on_spaces(stripped);
    if valid_parsed_input(parts) {
        if is_word_chain(parts[0], parts[1], parts[2]) {
            seq!['Y', 'E', 'S', '\n']
        } else {
            seq!['N', 'O', '\n']
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add uninterp attribute and fix split_string function */
#[verifier::uninterp]
spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

/* helper modified by LLM (iteration 5): Fix split_string function with proper decreases clause */
fn split_string(input: &Vec<char>) -> (parts: Vec<Vec<char>>)
    requires 
        input@.len() > 0,
        input@[input@.len() - 1] != ' ',
        input@[input@.len() - 1] != '\n'
    ensures 
        parts@.len() == 3,
        parts@[0].len() > 0,
        parts@[1].len() > 0,
        parts@[2].len() > 0
{
    let mut parts = Vec::new();
    let mut current = Vec::new();
    let mut count = 0;
    
    let mut i = 0;
    while i < input.len()
        invariant 
            count <= 3,
            i <= input@.len(),
            parts@.len() == count,
            current@.len() >= 0,
            count < 3 || (count == 3 && i == input@.len())
        decreases input@.len() - i
    {
        if input[i] == ' ' && current.len() > 0 {
            parts.push(current);
            count = count + 1;
            current = Vec::new();
            
            if count >= 3 {
                break;
            }
        } else if input[i] != ' ' {
            current.push(input[i]);
        }
        
        i = i + 1;
    }
    
    if current.len() > 0 && count < 3 {
        parts.push(current);
    }
    
    parts
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Properly handle the case when split_string doesn't return exactly 3 parts */
{
    let mut stripped_input = input.clone();
    if input.len() > 0 && input[input.len() - 1] == '\n' {
        stripped_input.pop();
    }
    
    let parts = split_string(&stripped_input);
    
    if parts.len() != 3 {
        return Vec::new();
    }
    
    let a = &parts[0];
    let b = &parts[1];
    let c = &parts[2];
    
    let is_chain = if a.len() > 0 && b.len() > 0 && c.len() > 0 {
        a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
    } else {
        false
    };
    
    let mut result = Vec::new();
    if is_chain {
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
    } else {
        result.push('N');
        result.push('O');
        result.push('\n');
    }
    
    result
}
// </vc-code>


}

fn main() {}