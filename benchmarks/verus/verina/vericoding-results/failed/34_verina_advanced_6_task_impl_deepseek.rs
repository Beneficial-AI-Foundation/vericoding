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
proof fn lemma_contains_all_vowels(s: Seq<char>) requires s == normalize_str(s) ensures s@.contains('a') && s@.contains('e') && s@.contains('i') && s@.contains('o') && s@.contains('u') <==> (forall c: char | #[trigger] s@.contains(c) ==> c=='a' || c=='e' || c=='i' || c=='o' || c=='u') { }
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
    proof {
        lemma_contains_all_vowels(normalize_str(s));
    }
    let s_lower = normalize_str(s);
    s_lower@.contains('a') && 
    s_lower@.contains('e') && 
    s_lower@.contains('i') && 
    s_lower@.contains('o') && 
    s_lower@.contains('u')
}
// </vc-code>

}
fn main() {}