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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): inlined is_vowel_exec logic */
    let mut result = Vec::new();
    if s.len() == 0 {
        return result;
    }
    result.push(s[0]);
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            result@.len() >= 1,
            result@[0] == s@[0],
            result@.len() <= i,
            no_consecutive_vowels(result@),
        decreases s.len() - i
    {
        let c = s[i];
        let last = result[result.len()-1];
        if (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y') && (last == 'a' || last == 'e' || last == 'i' || last == 'o' || last == 'u' || last == 'y') {
            // skip
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}