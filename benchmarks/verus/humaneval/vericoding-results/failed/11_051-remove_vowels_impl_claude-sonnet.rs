// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added exec mode function to call from main code */
fn is_vowel(c: char) -> (result: bool)
    ensures
        result == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop body to maintain invariant by proving filter properties */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i
    {
        let c = str[i];
        proof {
            assert(str@.subrange(0, i as int + 1) == str@.subrange(0, i as int).push(str@[i as int]));
            if !is_vowel_spec(c) {
                assert(str@.subrange(0, i as int + 1).filter(|x: char| !is_vowel_spec(x)) == 
                       str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)).push(c));
            } else {
                assert(str@.subrange(0, i as int + 1).filter(|x: char| !is_vowel_spec(x)) == 
                       str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)));
            }
        }
        if !is_vowel(c) {
            result.push(c);
        }
        i += 1;
    }
    proof {
        assert(i == str.len());
        assert(str@.subrange(0, i as int) == str@);
    }
    result
}
// </vc-code>

}
fn main() {}