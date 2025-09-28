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
spec fn contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

proof fn proof_normalize_str_to_lower(s: &str)
    ensures
        forall|i: int| 0 <= i < s.len() ==> normalize_str(s)[i] == to_lower(s.view()[i]),
{
    assert(normalize_str(s) == s.view().map_values(|c| to_lower(c)));
}

proof fn proof_to_lower_char_invariant(c: char)
    ensures
        ('A' <= c && c <= 'Z') ==> to_lower(c) as int == c as int + 32,
        !('A' <= c && c <= 'Z') ==> to_lower(c) == c,
{
    if 'A' <= c && c <= 'Z' {
        assert(to_lower(c) == ((c as int + 32) as char));
    } else {
        assert(to_lower(c) == c);
    }
}

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

proof fn proof_contains_char_normalize(s: &str, c: char)
    ensures
        contains_char(normalize_str(s), c) <==> contains_char(s.view().map_values(|c| to_lower(c)), c),
{
    assert(normalize_str(s) == s.view().map_values(|c| to_lower(c)));
}

proof fn proof_contains_char_to_lower(s: Seq<char>, c: char)
    ensures
        contains_char(s.map_values(|c| to_lower(c)), c) <==> exists|i: int| 0 <= i < s.len() && to_lower(s[i]) == c,
{
    assert(s.map_values(|c| to_lower(c)).len() == s.len());
}

proof fn proof_all_vowels_equivalence(s: &str)
    ensures
        (normalize_str(s).contains('a') &&
         normalize_str(s).contains('e') &&
         normalize_str(s).contains('i') &&
         normalize_str(s).contains('o') &&
         normalize_str(s).contains('u')) <==>
        (contains_char(normalize_str(s), 'a') &&
         contains_char(normalize_str(s), 'e') &&
         contains_char(normalize_str(s), 'i') &&
         contains_char(normalize_str(s), 'o') &&
         contains_char(normalize_str(s), 'u')),
{
    assert(normalize_str(s).contains('a') == contains_char(normalize_str(s), 'a'));
    assert(normalize_str(s).contains('e') == contains_char(normalize_str(s), 'e'));
    assert(normalize_str(s).contains('i') == contains_char(normalize_str(s), 'i'));
    assert(normalize_str(s).contains('o') == contains_char(normalize_str(s), 'o'));
    assert(normalize_str(s).contains('u') == contains_char(normalize_str(s), 'u'));
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
    let normalized = normalize_str(s);
    let has_a = normalized.contains('a');
    let has_e = normalized.contains('e');
    let has_i = normalized.contains('i');
    let has_o = normalized.contains('o');
    let has_u = normalized.contains('u');
    
    has_a && has_e && has_i && has_o && has_u
}
// </vc-code>

}
fn main() {}