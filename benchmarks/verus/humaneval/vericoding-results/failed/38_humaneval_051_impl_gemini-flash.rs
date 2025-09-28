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
/* helper modified by LLM (iteration 5): Removed the unterminated block comment error by closing the comment. The helper itself is not needed for the current iteration given the fixed code, so it's left empty. */

// </vc-helpers>

// <vc-spec>
fn remove_vowels(text: &str) -> (result: String)
    ensures valid_result(text@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed a compilation error by changing the type of `i` from `int` to `usize` for indexing and `len()` calls, which caused a type mismatch error and also caused the `decreases` clause to fail verification. */
    let mut result_string = String::new();
    let text_seq = text@;
    let mut i: usize = 0;
    let mut result_seq = Seq::<char>::new();

    while i < text_seq.len() 
        invariant
            i <= text_seq.len(),
            result_seq.len() <= i,
            // All characters in result_seq are consonants
            forall|idx: int| 0 <= idx < result_seq.len() ==> !is_vowel(result_seq[idx]),

            // result_seq is a subsequence of text_seq's consonants, maintaining relative order.
            // For any two chars in result_seq, they must appear in text_seq in the same order.
            forall|idx: int, jdx: int| #![trigger result_seq[idx], result_seq[jdx]]
                0 <= idx < jdx < result_seq.len() ==> 
                (exists|k: int, l: int|
                    0 <= k <= i as int && k < l <= i as int &&
                    text_seq[k] == result_seq[idx] && 
                    text_seq[l] == result_seq[jdx] &&
                    !is_vowel(text_seq[k]) && !is_vowel(text_seq[l])
                ),
            
            // Any consonant already processed (up to i-1) that is in text_seq is also in result_seq
            forall|char_idx: int|
                0 <= char_idx < i as int && !is_vowel(text_seq[char_idx]) ==> result_seq.contains(text_seq[char_idx]),

            // Any char in result_seq must have been in text_seq (up to i-1) and be a consonant
            forall|c: char| result_seq.contains(c) ==> text_seq.contains(c) && !is_vowel(c),

            // If all characters up to `i` were vowels, result_seq should be empty.
            (forall|k: int| 0 <= k < i as int ==> is_vowel(text_seq[k])) ==> result_seq.len() == 0

        decreases (text_seq.len() - i as int)
    {
        let c = text_seq[i as int];
        if !is_vowel(c) {
            result_string.push(c);
            result_seq = result_seq.push(c);
        }
        i = i + 1;
    }

    proof {
        // Final verification for valid_result
        assert(result_seq.len() <= text_seq.len());

        // All characters in final result are consonants
        assert(forall|idx: int| 0 <= idx < result_seq.len() ==> !is_vowel(result_seq[idx]));

        // Relative order of consonants is preserved, derived from invariant
        assert(forall|idx: int, jdx: int| #![trigger result_seq[idx], result_seq[jdx]]
            0 <= idx < jdx < result_seq.len() ==> 
            (exists|k: int, l: int|
                0 <= k < l < text_seq.len() &&
                text_seq[k] == result_seq[idx] && 
                text_seq[l] == result_seq[jdx] &&
                !is_vowel(text_seq[k]) && !is_vowel(text_seq[l])
            ));

        // If all text characters are vowels, result_seq length is 0
        if (forall|k: int| 0 <= k < text_seq.len() ==> is_vowel(text_seq[k])) {
            // The invariant handles this for `i = text_seq.len()`
            assert(result_seq.len() == 0);
        }
       
        // All consonants in original text are in result_seq
        assert(forall|char_idx: int| 0 <= char_idx < text_seq.len() && !is_vowel(text_seq[char_idx]) ==> result_seq.contains(text_seq[char_idx]));

        // Any char in result_seq must have been in text_seq and be a consonant
        assert(forall|c: char| result_seq.contains(c) ==> text_seq.contains(c) && !is_vowel(c));
    }

    result_string
}
// </vc-code>


}

fn main() {}