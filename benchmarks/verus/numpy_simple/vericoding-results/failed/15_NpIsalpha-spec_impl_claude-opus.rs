// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_alpha_char_exec(c: char) -> (ret: bool)
    ensures
        ret == is_alpha_char(c)
{
    (('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z'))
}

fn string_is_alpha_exec(s: &str) -> (ret: bool)
    ensures
        ret == string_is_alpha(s@)
{
    /* helper modified by LLM (iteration 5): fixed nat usage - using usize for exec code */
    if s@.len() == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_alpha_char(s@[j])
    {
        let c = s@[i as int];
        if !is_alpha_char_exec(c) {
            return false;
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 5): implementation unchanged */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < input.len()
        invariant
            0 <= i <= input.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == string_is_alpha(input[j]@)
    {
        let s_str: &str = input[i].as_str();
        let is_alpha_result = string_is_alpha_exec(s_str);
        result.push(is_alpha_result);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}