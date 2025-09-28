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
/* helper modified by LLM (iteration 5): executable vowel check consistent with spec is_vowel */
fn is_vowel_exec(c: char) -> (r: bool)
    ensures
        r == is_vowel(c),
{
    let lc = c;
    let res = lc == 'a' || lc == 'e' || lc == 'i' || lc == 'o' || lc == 'u'
        || lc == 'A' || lc == 'E' || lc == 'I' || lc == 'O' || lc == 'U';
    res
}

// </vc-helpers>

// <vc-spec>
fn remove_vowels(text: &str) -> (result: String)
    ensures valid_result(text@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use String::new to avoid unsupported String::from */
    let mut result = String::new();
    for c in text.chars() {
        if !is_vowel_exec(c) {
            result.push(c);
        }
    }
    result
}
// </vc-code>


}

fn main() {}