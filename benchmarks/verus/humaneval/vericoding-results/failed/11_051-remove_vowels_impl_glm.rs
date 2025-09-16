// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
exec fn is_vowel_exec(c: char) -> bool {
        c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
            || c == 'O' || c == 'U'
    }
    /* helper modified by LLM (iteration 3): added reveal and assert to prove equivalence */
    proof fn is_vowel_exec_equiv(c: char)
        ensures
            is_vowel_exec(c) == is_vowel_spec(c),
    {
        reveal(is_vowel_exec);
        assert(is_vowel_exec(c) == (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'));
    }
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed helper lemma to use reveal */
    let mut i: usize = 0;
    let mut result = Vec::new();
    while i < str.len()
        invariant
            0 <= i <= str@.len(),
            result@ == str@.take(i as int).filter(|x| !is_vowel_spec(x)),
        decreases str.len() - i,
    {
        if !is_vowel_exec(str[i]) {
            result.push(str[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}