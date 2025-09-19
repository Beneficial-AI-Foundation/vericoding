// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn get_vowel_replacement(c: char) -> char
    recommends is_vowel(c)
{
    if c == 'a' { 'c' }
    else if c == 'e' { 'g' }
    else if c == 'i' { 'k' }
    else if c == 'o' { 'q' }
    else if c == 'u' { 'w' }
    else if c == 'A' { 'C' }
    else if c == 'E' { 'G' }
    else if c == 'I' { 'K' }
    else if c == 'O' { 'Q' }
    else if c == 'U' { 'W' }
    else { c }
}

spec fn swap_case(c: char) -> char {
    if 'a' <= c && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn encode(message: Vec<char>) -> (result: Vec<char>)
    requires forall|i: int| 0 <= i < message@.len() ==> 
        (('a' <= message@[i] && message@[i] <= 'z') || 
         ('A' <= message@[i] && message@[i] <= 'Z') || 
         message@[i] == ' ')
    ensures result@.len() == message@.len(),
            forall|i: int| 0 <= i < message@.len() ==> 
                if #[trigger] message@[i] == ' ' {
                    #[trigger] result@[i] == ' '
                } else if is_vowel(#[trigger] message@[i]) {
                    result@[i] == swap_case(#[trigger] get_vowel_replacement(#[trigger] message@[i]))
                } else {
                    #[trigger] result@[i] == swap_case(#[trigger] message@[i])
                }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}