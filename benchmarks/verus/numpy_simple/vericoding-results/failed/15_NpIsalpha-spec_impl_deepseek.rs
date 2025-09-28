// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicates - helpers only in this section */
spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn string_is_alpha(s: Seq<char>) -> bool {
    if s.len() == 0 {
        false
    } else {
        forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn string_is_alpha(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
}

fn is_alpha(input: Vec<String>) -> (ret: Vec<bool>)
    ensures
        ret.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            ret[i] == string_is_alpha(input[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implemented using helper functions */
    let mut result = Vec::with_capacity(input.len());
    let mut idx = 0;
    
    while idx < input.len()
        invariant
            0 <= idx <= input.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == string_is_alpha(input[i]@)
    {
        let current_string = &input[idx];
        let mut is_alpha_string = current_string.len() > 0;
        let mut char_idx = 0;
        
        while char_idx < current_string.len()
            invariant
                0 <= char_idx <= current_string.len(),
                is_alpha_string == (current_string.len() > 0 && forall|j: int| 0 <= j < char_idx ==> is_alpha_char(current_string@[j]))
        {
            let current_char = current_string.as_str().chars().nth(char_idx).unwrap();
            if !is_alpha_char(current_char) {
                is_alpha_string = false;
                break;
            }
            char_idx += 1;
        }
        
        result.push(is_alpha_string);
        idx += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}