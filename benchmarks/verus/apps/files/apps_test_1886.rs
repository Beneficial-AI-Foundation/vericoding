// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(word: Seq<char>) -> bool {
    word.len() > 0 && forall|i: int| 0 <= i < word.len() ==> 
        (('a' <= word[i] && word[i] <= 'z') || ('A' <= word[i] && word[i] <= 'Z'))
}

spec fn correct_capitalization(input: Seq<char>, output: Seq<char>) -> bool {
    valid_input(input) ==> (
        output.len() == input.len() &&
        ('A' <= output[0] && output[0] <= 'Z') &&
        (('a' <= input[0] && input[0] <= 'z') ==> ('A' <= output[0] && output[0] <= 'Z')) &&
        (('A' <= input[0] && input[0] <= 'Z') ==> (output[0] == input[0])) &&
        forall|i: int| 1 <= i < input.len() ==> output[i] == input[i]
    )
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn capitalize_first_letter(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures correct_capitalization(word@, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}