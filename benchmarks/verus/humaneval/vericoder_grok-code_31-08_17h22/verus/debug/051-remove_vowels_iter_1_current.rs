use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>

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
            result@ == str@.subrange(0, i as int).filter(|c: char| !is_vowel_spec(c)),
    {
        if !is_vowel_spec(str[i]) {
            result.push(str[i]);
            assert(result@ == str@.subrange(0, (i + 1) as int).filter(|c: char| !is_vowel_spec(c)));
        } else {
            assert(result@ == str@.subrange(0, (i + 1) as int).filter(|c: char| !is_vowel_spec(c)));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}