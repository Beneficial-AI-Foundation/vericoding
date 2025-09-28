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
/* helper modified by LLM (iteration 4): Added exec versions of spec functions */
fn is_vowel_exec(c: char) -> (result: bool)
    ensures result == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

fn get_vowel_replacement_exec(c: char) -> (result: char)
    requires is_vowel(c)
    ensures result == get_vowel_replacement(c)
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

fn swap_case_exec(c: char) -> (result: char)
    ensures result == swap_case(c)
{
    if 'a' <= c && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}
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
    /* code modified by LLM (iteration 4): Fixed invariant maintenance by asserting precondition preservation */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < message.len()
        invariant
            0 <= i <= message.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < message.len() ==> 
                (('a' <= message@[j] && message@[j] <= 'z') || 
                 ('A' <= message@[j] && message@[j] <= 'Z') || 
                 message@[j] == ' '),
            forall|j: int| 0 <= j < i ==> 
                if message@[j] == ' ' {
                    result@[j] == ' '
                } else if is_vowel(message@[j]) {
                    result@[j] == swap_case(get_vowel_replacement(message@[j]))
                } else {
                    result@[j] == swap_case(message@[j])
                },
        decreases message.len() - i
    {
        let c = message[i];
        
        assert(('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == ' ');
        
        if c == ' ' {
            result.push(' ');
        } else if is_vowel_exec(c) {
            let replacement = get_vowel_replacement_exec(c);
            let swapped = swap_case_exec(replacement);
            result.push(swapped);
        } else {
            let swapped = swap_case_exec(c);
            result.push(swapped);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}