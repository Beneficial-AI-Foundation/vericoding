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
fn to_lower_exec(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        let code: u32 = c as u32;
        let lowered: char = (code + 32) as char;
        lowered
    } else {
        c
    }
}

spec fn is_vowel(c: char) -> bool { c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' }
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
    let mut found_a = false;
    let mut found_e = false;
    let mut found_i = false;
    let mut found_o = false;
    let mut found_u = false;

    for ch in s.chars() {
        let d = to_lower_exec(ch);
        if d == 'a' { found_a = true; }
        if d == 'e' { found_e = true; }
        if d == 'i' { found_i = true; }
        if d == 'o' { found_o = true; }
        if d == 'u' { found_u = true; }
    }

    let result = found_a && found_e && found_i && found_o && found_u;
    result
}
// </vc-code>

}
fn main() {}