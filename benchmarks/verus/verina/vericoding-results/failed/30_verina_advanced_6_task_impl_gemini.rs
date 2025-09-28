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
/* helper modified by LLM (iteration 5): keeping correct helper */
fn to_lower_char(c: char) -> (lower: char)
    ensures lower == to_lower(c),
{
    if 'A' <= c && c <= 'Z' {
        (c as u32 + 32) as char
    } else {
        c
    }
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
/* code modified by LLM (iteration 5): used correct lemma to relate chars and view */
{
    let mut has_a = false;
    let mut has_e = false;
    let mut has_i = false;
    let mut has_o = false;
    let mut has_u = false;

    let chars: Vec<char> = s.chars().collect();
    proof {
        vstd::string::lemma_chars_values_is_view(s);
    }

    let mut i: usize = 0;
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            has_a <==> s.view().subrange(0, i as int).map_values(|c: char| to_lower(c)).contains('a'),
            has_e <==> s.view().subrange(0, i as int).map_values(|c: char| to_lower(c)).contains('e'),
            has_i <==> s.view().subrange(0, i as int).map_values(|c: char| to_lower(c)).contains('i'),
            has_o <==> s.view().subrange(0, i as int).map_values(|c: char| to_lower(c)).contains('o'),
            has_u <==> s.view().subrange(0, i as int).map_values(|c: char| to_lower(c)).contains('u'),
        decreases chars.len() - i,
    {
        let c = chars[i];
        let lower_c = to_lower_char(c);

        if lower_c == 'a' {
            has_a = true;
        }
        if lower_c == 'e' {
            has_e = true;
        }
        if lower_c == 'i' {
            has_i = true;
        }
        if lower_c == 'o' {
            has_o = true;
        }
        if lower_c == 'u' {
            has_u = true;
        }
        
        i = i + 1;
    }

    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}