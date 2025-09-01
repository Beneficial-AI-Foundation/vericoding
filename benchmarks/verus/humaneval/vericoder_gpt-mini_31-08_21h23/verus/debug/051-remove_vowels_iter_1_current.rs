use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
// No helpers needed for this proof.
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
    let mut res = Vec::<char>::new();
    let mut i: nat = 0;
    while i < str.len() {
        invariant i <= str.len();
        invariant res@ == str@.slice(0, i).filter(|x: char| !is_vowel_spec(x));
        let c = str[i];
        if !is_vowel_spec(c) {
            res.push(c);
        }
        i += 1;
    }
    // At loop exit i == str.len(), so the invariant gives the desired postcondition.
    res
}
// </vc-code>

} // verus!
fn main() {}