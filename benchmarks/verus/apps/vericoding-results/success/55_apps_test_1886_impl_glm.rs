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
/* helper modified by LLM (iteration 3): fixed ensures clause to use implications instead of conditional expression */
fn char_to_upper(c: char) -> (result: char)
    requires 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z'
    ensures
        ('a' <= c && c <= 'z') ==> ('A' <= result && result <= 'Z' && (result as int) == (c as int) - ('a' as int) + 'A' as int),
        ('A' <= c && c <= 'Z') ==> (result == c)
{
    if 'a' <= c && c <= 'z' {
        let offset = (c as u8) - ('a' as u8);
        (('A' as u8) + offset) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn capitalize_first_letter(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures correct_capitalization(word@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed */
    let mut result = word;
    result[0] = char_to_upper(result[0]);
    result
}
// </vc-code>


}

fn main() {}