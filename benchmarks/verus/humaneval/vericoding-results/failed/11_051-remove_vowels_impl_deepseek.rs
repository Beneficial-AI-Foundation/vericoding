// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add decreases clause to recursive lemma */
proof fn filter_lemma(s: Seq<char>, i: int) 
    ensures 
        i >= 0 && i <= s.len(),
        s.filter(|x: char| !is_vowel_spec(x)).subrange(0, i as int) == s.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x))
    decreases i
{
    if i > 0 {
        filter_lemma(s, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use proof block with lemma to help verification */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < str.len()
        invariant
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x))
        decreases str.len() - i
    {
        proof {
            filter_lemma(str@, i as int);
        }
        let c = str[i];
        if !(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U') {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}