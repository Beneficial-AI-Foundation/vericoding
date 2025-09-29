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
spec fn encode_char_spec(c: char) -> char {
    if c == ' ' { ' ' }
    else if is_vowel(c) { swap_case(get_vowel_replacement(c)) }
    else { swap_case(c) }
}

fn is_vowel_exec(c: char) -> (r: bool)
    ensures r == is_vowel(c)
{
    let r = c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
            c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U';
    r
}

fn get_vowel_replacement_exec(c: char) -> (r: char)
    requires is_vowel(c)
    ensures r == get_vowel_replacement(c)
{
    let r = if c == 'a' { 'c' }
        else if c == 'e' { 'g' }
        else if c == 'i' { 'k' }
        else if c == 'o' { 'q' }
        else if c == 'u' { 'w' }
        else if c == 'A' { 'C' }
        else if c == 'E' { 'G' }
        else if c == 'I' { 'K' }
        else if c == 'O' { 'Q' }
        else if c == 'U' { 'W' }
        else { c };
    r
}

fn swap_case_exec(c: char) -> (r: char)
    ensures r == swap_case(c)
{
    let r = if 'a' <= c && c <= 'z' {
        ((c as u8 - 'a' as u8 + 'A' as u8) as char)
    } else if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    };
    r
}

fn encode_char(c: char) -> (r: char)
    ensures r == encode_char_spec(c)
{
    if c == ' ' {
        ' '
    } else {
        let v = is_vowel_exec(c);
        if v {
            let repl = get_vowel_replacement_exec(c);
            swap_case_exec(repl)
        } else {
            swap_case_exec(c)
        }
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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < message.len()
        invariant
            i <= message.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> result@[j] == encode_char_spec(message@[j]),
        decreases message.len() - i
    {
        let c = message[i];
        let r = encode_char(c);
        result.push(r);
        proof {
            let j = i as int;
            assert(result@.len() == j + 1);
            assert(result@[j] == r);
            assert(r == encode_char_spec(message@[j]));
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}