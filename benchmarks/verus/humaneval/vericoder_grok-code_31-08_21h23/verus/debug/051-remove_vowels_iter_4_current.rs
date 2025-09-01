use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
fn is_vowel(c: char) -> (b: bool)
    ensures
        b == is_vowel_spec(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
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
    let str_seq = str@;
    let str_len = str.len();
    let mut i: usize = 0;
    while i < str_len
        invariant
            i as nat >= 0,
            i as nat <= str_seq.len(),
            result@.len() == i as nat,
            result@ == str_seq.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x))
        decreases str_seq.len() - i as nat
    {
        let c = str[i];
        if !is_vowel(c) {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}