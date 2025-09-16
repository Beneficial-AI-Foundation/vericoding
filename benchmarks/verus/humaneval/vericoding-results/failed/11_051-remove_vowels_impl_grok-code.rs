// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Fixed compilation errors by using nat literals (0nat, 1nat), changing += to = ... + 1nat for index, and ensuring proper casting for subrange indices. */
    let mut result = Vec::new();
    let mut index: nat = 0nat;
    while index < str@.len()
        invariant
            index <= str@.len(),
            result@ == str@.subrange(0 as int, index as int).filter(|c: char| !is_vowel_spec(c)),
        decreases str@.len() as int - index as int
    {
        let c = str@[index];
        if !is_vowel_spec(c) {
            result.push(c);
            proof {
                assert(result@.subrange(0 as int, (index + 1nat) as int) == result@.subrange(0 as int, index as int).push(c));
                assert(str@.subrange(0 as int, (index + 1nat) as int).filter(|x: char| !is_vowel_spec(x))
                    == str@.subrange(0 as int, index as int).filter(|x: char| !is_vowel_spec(x)).push(c));
            }
        } else {
            proof {
                assert(str@.subrange(0 as int, (index + 1nat) as int).filter(|x: char| !is_vowel_spec(x))
                    == str@.subrange(0 as int, index as int).filter(|x: char| !is_vowel_spec(x)));
            }
        }
        index = index + 1nat;
    }
    result
}
// </vc-code>

}
fn main() {}