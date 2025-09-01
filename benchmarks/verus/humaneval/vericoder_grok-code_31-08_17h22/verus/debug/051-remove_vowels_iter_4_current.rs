use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
fn is_vowel(c: char) -> (result: bool)
    ensures
        result == (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
            || c == 'O' || c == 'U'),
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
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < str.len()
        invariant
            0 <= i <= str@.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases (str@.len() - i as int),
    {
        let is_v = is_vowel(str[i]);
        if !is_v {
            assert(!is_vowel_spec(str[i]));
            result.push(str[i]);
            assert(result@ == str@.subrange(0, (i + 1) as int).filter(|x: char| !is_vowel_spec(x)));
        } else {
            assert(is_vowel_spec(str[i]));
            assert(result@ == str@.subrange(0, (i + 1) as int).filter(|x: char| !is_vowel_spec(x)));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}