// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime vowel predicate for use in executable code */
fn is_vowel(c: char) -> bool { c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' }
/* helper modified by LLM (iteration 5): spec predicate for non-vowels */
spec fn not_vowel(c: char) -> bool { !is_vowel_spec(c) }
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using usize indices and build result, using runtime is_vowel for checks */
    let mut i: usize = 0;
    let n: usize = str.len();
    let mut res: Vec<char> = Vec::new();
    while i < n
        invariant
            i <= n,
            res@ == str@[0..i].filter(|x: char| !is_vowel_spec(x)),
        decreases n - i
    {
        let ch: char = str[i];
        if !is_vowel(ch) {
            res.push(ch);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}