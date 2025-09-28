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
fn flip_char_exec(c: char) -> (res: char)
    ensures res == flip_char(c),
{
    let c_u8 = c as u8;
    if 'a' <= c && c <= 'z' {
        (c_u8 - ('a' as u8) + ('A' as u8)) as char
    } else if 'A' <= c && c <= 'Z' {
        (c_u8 - ('A' as u8) + ('a' as u8)) as char
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == flip_char(s@[j]),
        decreases s.len() - i
    {
        let c = s[i];
        let flipped_c = flip_char_exec(c);
        result.push(flipped_c);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}