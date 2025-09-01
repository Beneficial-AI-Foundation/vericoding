use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
// No helpers needed for the fix, as the `is_vowel_spec` is provided in the preamble.
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
    let mut i: usize = 0; // Change to usize because array indexing requires usize

    while i < str.len()
        invariant
            0 <= i && i <= str.len(), // Use logical AND for combined conditions.
            result@ == str@.subsequence(0, i as nat).filter(|c: char| !is_vowel_spec(c)),
    {
        let current_char = str[i]; // i is already usize, so no need for 'as nat'
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