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
/* helper modified by LLM (iteration 5): Fixed compilation errors by avoiding .as_bytes() in helpers and using proper character handling */
spec fn string_contains_char(s: &str, target: char) -> bool {
    s.view().contains(target)
}

proof fn lemma_normalize_contains_equivalence(s: &str, c: char)
    ensures
        normalize_str(s).contains(to_lower(c)) <==> string_contains_char(s, c),
{
    assert forall |i: int| 0 <= i < s.view().len() implies #[trigger] normalize_str(s).index(i) == to_lower(s.view().index(i)) by {
        assert(normalize_str(s).index(i) == to_lower(s.view().index(i)));
    };
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
    /* code modified by LLM (iteration 5): Fixed compilation error by avoiding as_bytes() and using character iteration */
    let mut has_a = false;
    let mut has_e = false;
    let mut has_i = false;
    let mut has_o = false;
    let mut has_u = false;
    
    let chars = s.chars();
    let mut iter = chars.into_iter();
    
    while let Some(c) = iter.next()
        invariant
            has_a <==> exists |c_char| c_char == 'a' && string_contains_char(s, c_char),
            has_e <==> exists |c_char| c_char == 'e' && string_contains_char(s, c_char),
            has_i <==> exists |c_char| c_char == 'i' && string_contains_char(s, c_char),
            has_o <==> exists |c_char| c_char == 'o' && string_contains_char(s, c_char),
            has_u <==> exists |c_char| c_char == 'u' && string_contains_char(s, c_char),
    {
        let lower_c = to_lower(c);
        
        match lower_c {
            'a' => has_a = true,
            'e' => has_e = true,
            'i' => has_i = true,
            'O' => has_o = true,
            'u' => has_u = true,
            _ => {},
        }
    }
    
    lemma_normalize_contains_equivalence(s, 'a');
    lemma_normalize_contains_equivalence(s, 'e');
    lemma_normalize_contains_equivalence(s, 'i');
    lemma_normalize_contains_equivalence(s, 'o');
    lemma_normalize_contains_equivalence(s, 'u');
    
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}