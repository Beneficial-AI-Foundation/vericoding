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
    let mut res = Vec::new();
    let mut i = 0;
    while i < str.len() {
        // invariant: res@ == seq![str@[j] for j in 0..i if !is_vowel_spec(str@[j])]
        if !is_vowel_spec(str[i]) {
            res.push(str[i]);
        }
        i = i + 1;
        assert(res@ == seq![str@[j] for j in 0..i if(!is_vowel_spec(str@[j]))]);
    }
    res
}
// </vc-code>

} // verus!
fn main() {}