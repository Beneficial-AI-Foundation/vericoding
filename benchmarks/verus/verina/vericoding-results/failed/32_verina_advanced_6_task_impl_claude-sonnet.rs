// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as int + 32) as char)
    } else {
        c
    }
}

spec fn normalize_str(s: &str) -> Seq<char> {
    s.view().map_values(|c| to_lower(c))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by using vstd string operations */
fn contains_vowel(s: &str, vowel: char) -> (result: bool)
    requires
        vowel == 'a' || vowel == 'e' || vowel == 'i' || vowel == 'o' || vowel == 'u',
    ensures
        result <==> normalize_str(s).contains(vowel),
{
    let ghost s_view = s@;
    let mut i: usize = 0;
    while i < s_view.len()
        invariant
            0 <= i <= s_view.len(),
            !normalize_str(s).subrange(0, i as int).contains(vowel),
    {
        let c = s_view[i as int];
        let lower_c = if 'A' <= c && c <= 'Z' {
            ((c as int + 32) as char)
        } else {
            c
        };
        if lower_c == vowel {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn all_vowels(s: &str) -> (result: bool)
    ensures
        result <==> (
            normalize_str(s).contains('a') &&
            normalize_str(s).contains('e') &&
            normalize_str(s).contains('i') &&
            normalize_str(s).contains('o') &&
            normalize_str(s).contains('u')
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using helper function to check each vowel */
    contains_vowel(s, 'a') &&
    contains_vowel(s, 'e') &&
    contains_vowel(s, 'i') &&
    contains_vowel(s, 'o') &&
    contains_vowel(s, 'u')
}
// </vc-code>

}
fn main() {}