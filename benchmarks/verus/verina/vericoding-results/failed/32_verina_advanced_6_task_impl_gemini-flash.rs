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
/* helper modified by LLM (iteration 5): [removed the helper function as it was not used and the `to_lower` was a spec function which cannot be used in code in a previous iteration This helper is not needed as the logic is implemented directly in the `all_vowels` function] */
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
/* code modified by LLM (iteration 5): [changed `to_lower` to `v_to_lower` and made sure it's executable for use within the function and removed `is_vowel` calls from this code] */
{
    let mut has_a: bool = false;
    let mut has_e: bool = false;
    let mut has_i: bool = false;
    let mut has_o: bool = false;
    let mut has_u: bool = false;

    for c_char in s.chars() {
        let lowered_c: char = if 'A' <= c_char && c_char <= 'Z' {
            ((c_char as int + 32) as char)
        } else {
            c_char
        };

        if lowered_c == 'a' {
            has_a = true;
        } else if lowered_c == 'e' {
            has_e = true;
        } else if lowered_c == 'i' {
            has_i = true;
        } else if lowered_c == 'o' {
            has_o = true;
        } else if lowered_c == 'u' {
            has_u = true;
        }
    }
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}