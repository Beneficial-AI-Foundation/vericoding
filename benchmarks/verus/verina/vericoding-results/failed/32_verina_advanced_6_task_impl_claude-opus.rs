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
/* helper modified by LLM (iteration 3): fixed to_lower call issue by creating exec version */
fn to_lower_exec(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - b'A' + b'a') as char)
    } else {
        c
    }
}

fn check_contains_vowel(s: &str, vowel: char) -> (result: bool)
    ensures result <==> normalize_str(s).contains(to_lower(vowel))
{
    let mut i: usize = 0;
    let mut found = false;
    while i < s.unicode_len()
        invariant
            i <= s.unicode_len(),
            found <==> exists|j: int| 0 <= j < i && normalize_str(s)[j] == to_lower(vowel),
    {
        let c = s.get_char(i);
        if to_lower_exec(c) == to_lower_exec(vowel) {
            assert(to_lower_exec(c) == to_lower(c));
            assert(to_lower_exec(vowel) == to_lower(vowel));
            assert(normalize_str(s)[i as int] == to_lower(c));
            found = true;
        }
        i = i + 1;
    }
    assert(normalize_str(s).len() == s.unicode_len());
    found
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
    /* code modified by LLM (iteration 3): call helper functions to check for each vowel */
    let has_a = check_contains_vowel(s, 'a');
    let has_e = check_contains_vowel(s, 'e');
    let has_i = check_contains_vowel(s, 'i');
    let has_o = check_contains_vowel(s, 'o');
    let has_u = check_contains_vowel(s, 'u');
    
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}