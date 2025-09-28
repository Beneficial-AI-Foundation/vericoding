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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < word.len()
        invariant
            0 <= i <= word.len(),
            i == result.len(),
            i > 0 ==> result@[0] == if 'a' <= word@[0] && word@[0] <= 'z' {
                ((word@[0] as u8 - 'a' as u8 + 'A' as u8) as char)
            } else {
                word@[0]
            },
            forall|j: int| 1 <= j < i ==> result@[j] == word@[j],
        decreases word.len() - i
    {
        if i == 0 {
            let first_char = word[0];
            let capitalized = if 'a' <= first_char && first_char <= 'z' {
                ((first_char as u8 - 'a' as u8 + 'A' as u8) as char)
            } else {
                first_char
            };
            result.push(capitalized);
        } else {
            result.push(word[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}