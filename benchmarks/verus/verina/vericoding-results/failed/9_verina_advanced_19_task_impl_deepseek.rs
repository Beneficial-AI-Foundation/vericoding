// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_alpha(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn is_lower_alpha(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn is_alpha(c: char) -> bool {
    is_upper_alpha(c) || is_lower_alpha(c)
}

spec fn to_lower(c: char) -> char {
    if is_upper_alpha(c) {

        c
    } else {
        c
    }
}

spec fn normalize_char(c: char) -> Option<char> {
    if is_alpha(c) {
        Some(to_lower(c))
    } else {
        None
    }
}

spec fn normalize_string(s: &str) -> Seq<char> {
    s@.fold_left(Seq::empty(), |acc: Seq<char>, c: char|
        match normalize_char(c) {
            Some(c_norm) => acc.push(c_norm),
            None => acc,
        }
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors by removing problematic lemmas and adding proper sequence equality helper */
proof fn lemma_seq_reverse_equals_self<S>(s: Seq<S>)
    ensures s.reverse() == s
{
}

proof fn lemma_seq_equal<S>(s1: Seq<S>, s2: Seq<S>)
    ensures s1 == s2 <==> s1.len() == s2.len() && forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
{
}
// </vc-helpers>

// <vc-spec>
fn is_clean_palindrome(s: &str) -> (result: bool)
    ensures 
        result == (normalize_string(s) == normalize_string(s).reverse()),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches and proper sequence indexing */
{
    let normalized = normalize_string(s);
    let reversed = normalized.reverse();
    
    let mut result = true;
    let len = normalized.len() as usize;
    
    proof {
        lemma_seq_equal(normalized, reversed);
    }
    
    let mut i: usize = 0;
    while i < len {
        let idx = i as int;
        if normalized.index(idx) != reversed.index(idx) {
            result = false;
            break;
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}