// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() == 1 && 'a' <= input[0] && input[0] <= 'z'
}

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

spec fn expected_output(input: Seq<char>) -> Seq<char>
    recommends valid_input(input)
{
    if is_vowel(input[0]) { seq!['v', 'o', 'w', 'e', 'l'] } else { seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't'] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed ensures to name return value */
fn is_vowel_exec(c: char) -> (result: bool)
    ensures
        is_vowel(c) == result,
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@),
    ensures 
        result@ == expected_output(input@),
        result@ == seq!['v', 'o', 'w', 'e', 'l'] || result@ == seq!['c', 'o', 'n', 's', 'o', 'n', 'a', 'n', 't'],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement vowel/consonant logic using exec helper */
    let c = input[0];
    if is_vowel_exec(c) {
        let mut result = Vec::new();
        result.push('v');
        result.push('o');
        result.push('w');
        result.push('e');
        result.push('l');
        result
    } else {
        let mut result = Vec::new();
        result.push('c');
        result.push('o');
        result.push('n');
        result.push('s');
        result.push('o');
        result.push('n');
        result.push('a');
        result.push('n');
        result.push('t');
        result
    }
}
// </vc-code>


}

fn main() {}