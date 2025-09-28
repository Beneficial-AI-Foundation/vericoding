// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed `is_alphanumeric_char` definition. Removed spec keyword from the helper definition and added body to the function. */
fn is_alphanumeric_char(c: char) -> bool
{
    ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
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
/* code modified by LLM (iteration 5): Removed redundant spec fn declaration. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;

    while i < a.len()
        invariant
            result.len() == i,
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@))
    {
        let current_string_seq = a[i]@;
        let is_valid = current_string_seq.len() > 0 && all_chars_alphanumeric(current_string_seq);
        result.push(is_valid);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}