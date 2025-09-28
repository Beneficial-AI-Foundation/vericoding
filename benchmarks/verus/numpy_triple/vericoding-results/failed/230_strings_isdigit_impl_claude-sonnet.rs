// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate declaration and kept implementation */
spec fn all_chars_digit(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i].is_ascii_digit()
}

fn check_string_digits(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_digit(s@))
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j].is_ascii_digit()
    {
        if !s.as_bytes()[i].is_ascii_digit() {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == (a[i as int]@.len() > 0 && all_chars_digit(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using helper function to implement isdigit */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
    {
        let is_digit = check_string_digits(&a[i]);
        result.push(is_digit);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}