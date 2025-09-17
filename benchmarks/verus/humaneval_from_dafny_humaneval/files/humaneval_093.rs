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
fn encode(message: Seq<char>) -> (result: Seq<char>)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}