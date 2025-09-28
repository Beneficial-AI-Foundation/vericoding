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
spec fn is_lowercase(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn is_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

/* helper modified by LLM (iteration 2): changed u32 to u8 for char casting to fix compilation error */
fn to_uppercase(c: char) -> (res: char)
    requires
        is_lowercase(c),
    ensures
        is_uppercase(res),
        res as int == c as int - ('a' as int - 'A' as int),
{
    ((c as u8 - 'a' as u8) + 'A' as u8) as char
}
// </vc-helpers>

// <vc-spec>
fn capitalize_first_letter(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures correct_capitalization(word@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implementation unchanged, fix was in helper function */
    let mut result = word.clone();
    let first_char = word[0];

    if 'a' <= first_char && first_char <= 'z' {
        proof {
            assert(is_lowercase(first_char));
        }
        let upper_char = to_uppercase(first_char);
        result.set(0, upper_char);
    }

    result
}
// </vc-code>


}

fn main() {}