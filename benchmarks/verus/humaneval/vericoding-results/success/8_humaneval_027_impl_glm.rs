// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lowercase(c: char) -> bool {
    'a' <= c <= 'z'
}

spec fn is_uppercase(c: char) -> bool {
    'A' <= c <= 'Z'
}

spec fn flip_char(c: char) -> char {
    if is_lowercase(c) { 
        ((c as u8) - ('a' as u8) + ('A' as u8)) as char
    } else if is_uppercase(c) { 
        ((c as u8) - ('A' as u8) + ('a' as u8)) as char
    } else { 
        c 
    }
}

spec fn valid_flip_case(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() &&
    forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == #[trigger] flip_char( #[trigger] s[i])
}
// </vc-preamble>

// <vc-helpers>
fn flip_char_exec(c: char) -> (result: char)
    ensures result == flip_char(c)
{
    if 'a' <= c && c <= 'z' {
        let offset = (c as u8) - ('a' as u8);
        let new_char = ('A' as u8) + offset;
        new_char as char
    } else if 'A' <= c && c <= 'Z' {
        let offset = (c as u8) - ('A' as u8);
        let new_char = ('a' as u8) + offset;
        new_char as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn flip_case(s: Vec<char>) -> (result: Vec<char>)
    ensures valid_flip_case(s@, result@)
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let mut result = Vec::with_capacity(s.len());
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == flip_char(s@[j]),
        decreases s.len() - i
    {
        let c = s[i];
        let flipped = flip_char_exec(c);
        result.push(flipped);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}