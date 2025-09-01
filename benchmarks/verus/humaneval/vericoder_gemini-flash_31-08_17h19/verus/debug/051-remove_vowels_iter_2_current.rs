use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
spec fn is_vowel_spec(c: char) -> (result: bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    // post-conditions-start
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: int = 0;

    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result@ == str@.subsequence(0, i as nat).filter(|c: char| !is_vowel_spec(c)),
    {
        let current_char = str[i as nat];
        if !is_vowel_spec(current_char) {
            result.push(current_char);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}