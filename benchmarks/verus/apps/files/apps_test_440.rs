// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y'
}

spec fn no_consecutive_vowels(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> !(is_vowel(s[i]) && is_vowel(s[i+1]))
}

spec fn valid_output(input: Seq<char>, output: Seq<char>) -> bool {
    output.len() <= input.len() &&
    no_consecutive_vowels(output) &&
    (input.len() > 0 ==> output.len() > 0) &&
    (input.len() > 0 ==> output[0] == input[0])
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>) -> (result: Seq<char>)
    ensures valid_output(s, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}