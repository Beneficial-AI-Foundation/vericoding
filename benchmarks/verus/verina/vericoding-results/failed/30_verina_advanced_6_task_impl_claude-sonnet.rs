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
proof fn lemma_normalize_char_cases(c: char)
    ensures
        to_lower(c) == 'a' <==> (c == 'a' || c == 'A'),
        to_lower(c) == 'e' <==> (c == 'e' || c == 'E'),
        to_lower(c) == 'i' <==> (c == 'i' || c == 'I'),
        to_lower(c) == 'o' <==> (c == 'o' || c == 'O'),
        to_lower(c) == 'u' <==> (c == 'u' || c == 'U'),
{
}

proof fn lemma_normalize_contains_vowel(s: &str, vowel: char)
    requires
        vowel == 'a' || vowel == 'e' || vowel == 'i' || vowel == 'o' || vowel == 'u',
    ensures
        normalize_str(s).contains(vowel) <==> (
            exists|i: int| 0 <= i < s@.len() && to_lower(s@[i]) == vowel
        ),
{
    let normalized = normalize_str(s);
    if normalized.contains(vowel) {
        let i = choose|i: int| 0 <= i < normalized.len() && normalized[i] == vowel;
        assert(to_lower(s@[i]) == vowel);
    }
    if exists|i: int| 0 <= i < s@.len() && to_lower(s@[i]) == vowel {
        let i = choose|i: int| 0 <= i < s@.len() && to_lower(s@[i]) == vowel;
        assert(normalized[i] == vowel);
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
{
    /* code modified by LLM (iteration 5): use s@.len() instead of s.len() for length access */
    let mut has_a = false;
    let mut has_e = false;
    let mut has_i = false;
    let mut has_o = false;
    let mut has_u = false;
    
    let mut idx: usize = 0;
    while idx < s@.len()
        invariant
            0 <= idx <= s@.len(),
            has_a <==> (exists|i: int| 0 <= i < idx && to_lower(s@[i]) == 'a'),
            has_e <==> (exists|i: int| 0 <= i < idx && to_lower(s@[i]) == 'e'),
            has_i <==> (exists|i: int| 0 <= i < idx && to_lower(s@[i]) == 'i'),
            has_o <==> (exists|i: int| 0 <= i < idx && to_lower(s@[i]) == 'o'),
            has_u <==> (exists|i: int| 0 <= i < idx && to_lower(s@[i]) == 'u'),
        decreases s@.len() - idx
    {
        let c = s.get_char(idx);
        let lower_c = if 'A' <= c && c <= 'Z' {
            ((c as u8 + 32) as char)
        } else {
            c
        };
        
        proof {
            lemma_normalize_char_cases(c);
            assert(to_lower(c) == lower_c);
        }
        
        if lower_c == 'a' {
            has_a = true;
        } else if lower_c == 'e' {
            has_e = true;
        } else if lower_c == 'i' {
            has_i = true;
        } else if lower_c == 'o' {
            has_o = true;
        } else if lower_c == 'u' {
            has_u = true;
        }
        
        idx += 1;
    }
    
    proof {
        lemma_normalize_contains_vowel(s, 'a');
        lemma_normalize_contains_vowel(s, 'e');
        lemma_normalize_contains_vowel(s, 'i');
        lemma_normalize_contains_vowel(s, 'o');
        lemma_normalize_contains_vowel(s, 'u');
    }
    
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}