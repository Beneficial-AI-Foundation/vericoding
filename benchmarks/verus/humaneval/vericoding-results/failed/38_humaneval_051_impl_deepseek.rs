// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
        c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
        c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
    }
    
spec fn valid_result(text: Seq<char>, result: Seq<char>) -> bool {
        && result.len() <= text.len()
        && (forall|i: int| 0 <= i < result.len() ==> !is_vowel(result[i]))
        && (forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> 
            (exists|k: int, l: int| 0 <= k < l < text.len() && text[k] == result[i] && text[l] == result[j] &&
            !is_vowel(text[k]) && !is_vowel(text[l])))
        && ((forall|i: int| 0 <= i < text.len() ==> is_vowel(text[i])) ==> result.len() == 0)
        && (forall|i: int| 0 <= i < text.len() && !is_vowel(text[i]) ==> result.contains(text[i]))
        && (forall|c: char| result.contains(c) ==> text.contains(c) && !is_vowel(c))
    }
    
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed Seq::empty() type annotation and added proper proof logic */
proof fn lemma_filter_preserves_order(text: Seq<char>, pred: spec_fn(char) -> bool)
    requires
        text.len() >= 0,
    ensures
        forall|i: int, j: int| #![trigger text[i]] #![trigger text[j]] 0 <= i < j < text.len() && pred(text[i]) && pred(text[j]) ==> 
            (exists|k: int, l: int| 0 <= k < l < text.len() && text[k] == text[i] && text[l] == text[j]),
{
    assert forall|i: int, j: int| 0 <= i < j < text.len() && pred(text[i]) && pred(text[j]) implies 
        (exists|k: int, l: int| 0 <= k < l < text.len() && text[k] == text[i] && text[l] == text[j]) by {
        assert(text[i] == text[i]);
        assert(text[j] == text[j]);
    }
}

proof fn lemma_all_vowels_implies_empty_result(text: Seq<char>)
    requires
        forall|i: int| 0 <= i < text.len() ==> is_vowel(text[i]),
    ensures
        valid_result(text, Seq::empty::<char>()),
{
    assert(Seq::empty::<char>().len() <= text.len());
    assert(forall|i: int| 0 <= i < Seq::empty::<char>().len() ==> !is_vowel(Seq::empty::<char>()[i]));
    assert(forall|i: int| 0 <= i < text.len() && !is_vowel(text[i]) ==> Seq::empty::<char>().contains(text[i]));
    assert(forall|c: char| Seq::empty::<char>().contains(c) ==> text.contains(c) && !is_vowel(c));
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(text: &str) -> (result: String)
    ensures valid_result(text@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed lemma calls with type annotations */
    let mut result_chars = Vec::new();
    let text_chars: Vec<char> = text.chars().collect();
    let mut i: usize = 0;
    
    while i < text_chars.len()
        invariant
            result_chars@.len() <= i,
            forall|j: int| 0 <= j < result_chars@.len() ==> !is_vowel(result_chars@[j]),
            forall|j: int| 0 <= j < text_chars@.len() && !is_vowel(text_chars@[j]) ==> result_chars@.contains(text_chars@[j]),
            forall|c: char| result_chars@.contains(c) ==> text_chars@.contains(c) && !is_vowel(c),
    {
        let c = text_chars[i];
        if !is_vowel(c) {
            result_chars.push(c);
        }
        i += 1;
    }
    
    proof {
        lemma_filter_preserves_order(text_chars@, |c: char| !is_vowel(c));
        if forall|i: int| 0 <= i < text_chars@.len() ==> is_vowel(text_chars@[i]) {
            lemma_all_vowels_implies_empty_result(text_chars@);
        }
    }
    
    result_chars.into_iter().collect()
}
// </vc-code>


}

fn main() {}