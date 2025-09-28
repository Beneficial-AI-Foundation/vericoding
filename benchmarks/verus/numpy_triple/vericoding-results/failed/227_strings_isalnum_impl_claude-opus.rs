// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate spec function definition and external_body attribute */
fn is_alphanumeric_char_exec(c: char) -> (result: bool)
    ensures result == is_alphanumeric_char(c)
{
    c.is_ascii_alphanumeric()
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
    /* code modified by LLM (iteration 5): Fixed implementation to check all characters properly */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@))
    {
        let s = &a[i];
        let mut all_alnum = s@.len() > 0;
        if all_alnum {
            let chars: Vec<char> = s.chars().collect();
            let mut j = 0;
            let mut found_non_alnum = false;
            while j < chars.len()
                invariant
                    0 <= j <= chars.len(),
                    chars@.len() == s@.len(),
                    forall|k: int| 0 <= k < chars.len() ==> chars[k] == s@[k],
                    !found_non_alnum ==> forall|k: int| 0 <= k < j ==> is_alphanumeric_char(chars[k]),
                    found_non_alnum ==> exists|k: int| 0 <= k < j && !is_alphanumeric_char(chars[k])
            {
                if !is_alphanumeric_char_exec(chars[j]) {
                    found_non_alnum = true;
                    all_alnum = false;
                }
                j = j + 1;
            }
            if !found_non_alnum {
                assert(forall|k: int| 0 <= k < chars.len() ==> is_alphanumeric_char(chars[k]));
                assert(all_chars_alphanumeric(s@));
            }
        }
        result.push(all_alnum);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}