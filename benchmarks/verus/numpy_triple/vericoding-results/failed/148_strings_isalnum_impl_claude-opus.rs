// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate is_alphanumeric_char definition */
exec fn is_alphanumeric_char_exec(c: char) -> (result: bool)
    ensures result == is_alphanumeric_char(c)
{
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
}

exec fn all_chars_alphanumeric_exec(s: &Vec<char>) -> (result: bool)
    ensures result == all_chars_alphanumeric(s@)
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_alphanumeric_char(s@[j])
    {
        if !is_alphanumeric_char_exec(s[i]) {
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
/* code modified by LLM (iteration 5): using Vec<char> conversion for string checking */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@))
    {
        let s = &a[i];
        let chars: Vec<char> = s.chars().collect();
        let is_alnum = chars.len() > 0 && all_chars_alphanumeric_exec(&chars);
        result.push(is_alnum);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}