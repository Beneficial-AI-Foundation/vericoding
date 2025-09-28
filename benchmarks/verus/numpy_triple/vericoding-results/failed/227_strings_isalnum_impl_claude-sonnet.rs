// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate definition and fixed uninterp syntax */
spec fn is_alphanumeric_char(c: char) -> bool
{
    uninterp
}

fn check_string_alphanumeric(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_alphanumeric(s@))
{
    if s@.len() == 0 {
        return false;
    }
    
    let mut i = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int| 0 <= j < i ==> is_alphanumeric_char(s@[j])
    {
        let c = s@[i];
        if !is_alphanumeric_char(c) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed index casting issue */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@))
    {
        let is_valid = check_string_alphanumeric(&a[i]);
        result.push(is_valid);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}