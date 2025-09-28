// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}

spec fn no_consecutive_vowels(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> !(is_vowel(#[trigger] s[i]) && is_vowel(s[i+1]))
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool {
    output.len() <= input.len() &&
    no_consecutive_vowels(output) &&
    (input.len() > 0 ==> output.len() > 0) &&
    (input.len() > 0 ==> output[0] == input[0])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added exec function to check vowels at runtime */
fn is_vowel_exec(c: char) -> (result: bool)
    ensures result == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed invariants to ensure postcondition */
    if s.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    result.push(s[0]);
    
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            result.len() >= 1,
            result.len() <= i,
            result[0] == s[0],
            no_consecutive_vowels(result@),
        decreases s.len() - i
    {
        let last_char = result[result.len() - 1];
        let current_char = s[i];
        
        if !(is_vowel_exec(last_char) && is_vowel_exec(current_char)) {
            result.push(current_char);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}