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
/* helper modified by LLM (iteration 2): No changes required for helper function */
spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
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
/* code modified by LLM (iteration 2): Changed loop index type from nat to int */
{
    let normalized_s = normalize_str(s);
    let mut has_a = false;
    let mut has_e = false;
    let mut has_i = false;
    let mut has_o = false;
    let mut has_u = false;

    // Verus uses `int` for loop ranges when iterating over `Seq` lengths.
    for i in 0..normalized_s.len() as int {
        let c = normalized_s.index(i);
        if c == 'a' { has_a = true; }
        if c == 'e' { has_e = true; }
        if c == 'i' { has_i = true; }
        if c == 'o' { has_o = true; }
        if c == 'u' { has_u = true; }
    }

    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}