// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use direct character access via sequence indexing */
fn check_string_is_alpha(s: &String) -> (ret: bool)
    ensures
        ret == string_is_alpha(s@)
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_alpha_char(s@[j])
    {
        let c = s@[i as int];
        if !((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')) {
            return false;
        }
        i += 1;
    }
    true
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
    /* code modified by LLM (iteration 5): use helper function with proper character access */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_is_alpha(input[j]@)
    {
        let is_alpha_result = check_string_is_alpha(&input[i]);
        result.push(is_alpha_result);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}