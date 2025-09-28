// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix compilation errors by using string length and char_at method */
fn process_string(s: &String) -> (result: bool)
    ensures
        result == (string_has_cased_char(s@) && string_all_cased_are_lowercase(s@))
{
    let mut has_cased = false;
    let mut all_lower = true;
    let mut seen = Seq::<char>::empty();
    let len = s.len();
    let mut idx = 0;
    
    while idx < len
        invariant
            0 <= idx <= len,
            seen == s@.subrange(0, idx),
            has_cased == string_has_cased_char(seen),
            all_lower == (string_has_cased_char(seen) ==> string_all_cased_are_lowercase(seen))
        decreases
            len - idx
    {
        let c = s.char_at(idx);
        seen = seen.push(c);
        if is_alpha_char(c) {
            has_cased = true;
            if !is_lower_char(c) {
                all_lower = false;
            }
        }
        idx += 1;
    }
    
    has_cased && all_lower
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c <= 'z') || ('A' <= c <= 'Z')
}

spec fn is_lower_char(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn string_has_cased_char(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn string_all_cased_are_lowercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_lower_char(s[i])
}

fn islower(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i as int] == (string_has_cased_char(a[i]@) && string_all_cased_are_lowercase(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use explicit index to avoid iterator issues */
    let mut result = Vec::with_capacity(a.len());
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (string_has_cased_char(a[j]@) && string_all_cased_are_lowercase(a[j]@)),
        decreases
            a.len() - i
    {
        let s = &a[i];
        let is_lower = process_string(s);
        result.push(is_lower);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}