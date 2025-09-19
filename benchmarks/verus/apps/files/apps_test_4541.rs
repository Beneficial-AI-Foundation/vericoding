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
    /* impl-start */
    assume(false);
    unreached()
    /* impl-end */
}
// </vc-code>


}

fn main() {}