use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
fn is_vowel(c: char) -> (result: bool)
    ensures result == is_vowel_spec(c)
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
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i
    {
        if !is_vowel(str[i as int]) {
            result.push(str[i as int]);
            assert(result@.last() == str[i as int]);
            assert(!is_vowel_spec(str[i as int]));
        }
        i += 1;
        assert(str@.subrange(0, (i - 1) as int + 1) == str@.subrange(0, i as int));
    }
    
    assert(str@.subrange(0, i as int) == str@);
    result
}
// </vc-code>

} // verus!
fn main() {}