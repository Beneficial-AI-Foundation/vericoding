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

/* helper modified by LLM (iteration 3): removed requires/ensures from spec function */
spec fn to_uppercase_spec(c: char) -> char {
    ((c as u8) - ('a' as u8) + ('A' as u8)) as char
}

fn is_lowercase_exec(c: char) -> (result: bool)
    ensures result == is_lowercase(c)
{
    'a' <= c && c <= 'z'
}

fn to_uppercase(c: char) -> (result: char)
    requires is_lowercase(c)
    ensures result == to_uppercase_spec(c)
{
    let a_val = 'a' as u8;
    let big_a_val = 'A' as u8;
    let c_val = c as u8;
    let diff = c_val - a_val;
    let result_val = big_a_val + diff;
    result_val as char
}
// </vc-helpers>

// <vc-spec>
fn capitalize_first_letter(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures correct_capitalization(word@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use exec function for mode compatibility */
    let mut result = word;
    let first_char = result[0];
    
    if is_lowercase_exec(first_char) {
        result.set(0, to_uppercase(first_char));
    }
    
    result
}
// </vc-code>


}

fn main() {}