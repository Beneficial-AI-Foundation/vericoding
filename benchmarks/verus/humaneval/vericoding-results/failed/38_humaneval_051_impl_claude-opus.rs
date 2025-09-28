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

// </vc-helpers>

// <vc-spec>
fn remove_vowels(text: &str) -> (result: String)
    ensures valid_result(text@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing to use usize directly */
    let mut result_vec: Vec<char> = Vec::new();
    let text_seq = text@;
    
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            text@ == text_seq,
            forall|j: int| 0 <= j < result_vec.len() ==> !is_vowel(result_vec@[j]),
            forall|j: int| 0 <= j < i ==> (!is_vowel(text_seq[j]) ==> result_vec@.contains(text_seq[j])),
            forall|c: char| result_vec@.contains(c) ==> text_seq.contains(c) && !is_vowel(c),
    {
        let c = text.get_char(i);
        if !is_vowel(c) {
            if !result_vec@.contains(c) {
                result_vec.push(c);
            }
        }
        i = i + 1;
    }
    
    // Build result string from result_vec
    let mut result = String::new();
    let mut j: usize = 0;
    while j < result_vec.len()
        invariant
            j <= result_vec.len(),
            result@ == result_vec@.subrange(0, j as int),
    {
        result.push(result_vec[j]);
        j = j + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}