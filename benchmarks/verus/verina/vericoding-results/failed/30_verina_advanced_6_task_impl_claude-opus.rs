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
/* helper modified by LLM (iteration 3): Added decreases clause to while loop */
fn exec_to_lower(c: char) -> (result: char)
    ensures
        result == to_lower(c),
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8 + 32) as char)
    } else {
        c
    }
}

fn is_vowel(c: char) -> (result: bool)
    ensures
        result <==> (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

fn check_vowel_present(s: &str, vowel: char) -> (result: bool)
    requires
        vowel == 'a' || vowel == 'e' || vowel == 'i' || vowel == 'o' || vowel == 'u',
    ensures
        result <==> normalize_str(s).contains(vowel),
{
    let mut i: usize = 0;
    let mut found = false;
    let len = s.unicode_len();
    
    while i < len
        invariant
            0 <= i <= len,
            found <==> exists|j: int| 0 <= j < i && to_lower(s@[j]) == vowel,
        decreases len - i,
    {
        let c = s.get_char(i);
        let lower_c = exec_to_lower(c);
        if lower_c == vowel {
            found = true;
            proof {
                assert(s@[i as int] == c);
                assert(to_lower(c) == vowel);
            }
        }
        i = i + 1;
    }
    
    proof {
        if found {
            let witness = choose|j: int| 0 <= j < i && to_lower(s@[j]) == vowel;
            assert(normalize_str(s)[witness] == vowel);
            assert(normalize_str(s).contains(vowel));
        } else {
            assert(forall|j: int| 0 <= j < len ==> to_lower(s@[j]) != vowel);
            assert(!normalize_str(s).contains(vowel));
        }
    }
    
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
/* code modified by LLM (iteration 3): Using helper function to check for all vowels */
{
    let has_a = check_vowel_present(s, 'a');
    let has_e = check_vowel_present(s, 'e');
    let has_i = check_vowel_present(s, 'i');
    let has_o = check_vowel_present(s, 'o');
    let has_u = check_vowel_present(s, 'u');
    
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}