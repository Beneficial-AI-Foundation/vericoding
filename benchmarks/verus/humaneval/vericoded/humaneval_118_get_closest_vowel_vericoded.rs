// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn is_consonant(c: char) -> bool {
    (('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')) && !is_vowel(c)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn get_closest_vowel(word: Vec<char>) -> (result: Vec<char>)
    requires forall|i: int| 0 <= i < word.len() ==> (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z'))
    ensures ({
        &&& result.len() <= 1
        &&& (result.len() == 1 ==> is_vowel(result@[0]))
        &&& (result.len() == 1 ==> exists|i: int| 
            1 <= i && i + 1 < word.len()
                && is_vowel(word@[i]) && is_consonant(word@[i - 1]) && is_consonant(word@[i + 1])
                && (forall|j: int| i < j < word.len() - 1 ==> !is_vowel(word@[j]) || !is_consonant(word@[j - 1]) || !is_consonant(word@[j + 1])))
    })
// </vc-spec>
// <vc-code>
{
    let out: Vec<char> = Vec::new();
    out
}
// </vc-code>


}

fn main() {}