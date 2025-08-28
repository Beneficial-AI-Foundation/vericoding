use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
fn is_vowel(c: char) -> (is_vowel: bool)
    ensures
        is_vowel == is_vowel_spec(c),
{
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
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < str.len()
        invariant
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
    {
        if !is_vowel(str[i]) {
            result.push(str[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}