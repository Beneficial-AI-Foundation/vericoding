// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): directly using is_vowel_spec for clarity */
fn is_not_vowel(c: char) -> (result: bool)
    ensures
        result == !is_vowel_spec(c),
{
    !is_vowel_spec(c)
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): directly using is_vowel_spec for clearer verification */
    let mut result = Vec::new();
    for i in 0..str.len() {
        if !is_vowel_spec(str[i]) {
            result.push(str[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}