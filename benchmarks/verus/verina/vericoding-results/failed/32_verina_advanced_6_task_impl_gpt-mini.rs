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
/* helper modified by LLM (iteration 5): spec helper to check if s contains char ignoring case */
spec fn contains_ignore_case(s: &str, c: char) -> bool {
    let seq = normalize_str(s);
    seq.contains(c)
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
    /* code modified by LLM (iteration 5): compute result using runtime lowercase scan with u32 casts */
    let mut has_a = false;
    let mut has_e = false;
    let mut has_i = false;
    let mut has_o = false;
    let mut has_u = false;
    for c in s.chars() {
        let lc = if 'A' <= c && c <= 'Z' {
            ((c as u32 + 32) as char)
        } else {
            c
        };
        if lc == 'a' { has_a = true; }
        if lc == 'e' { has_e = true; }
        if lc == 'i' { has_i = true; }
        if lc == 'o' { has_o = true; }
        if lc == 'u' { has_u = true; }
    }
    let result = has_a && has_e && has_i && has_o && has_u;
    result
}
// </vc-code>

}
fn main() {}