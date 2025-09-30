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
fn exec_flip_char(c: char) -> (r: char)
    ensures
        r == flip_char(c),
{
    if 'a' <= c && c <= 'z' {
        let r0: char = (((c as u8) - ('a' as u8)) + ('A' as u8)) as char;
        r0
    } else if 'A' <= c && c <= 'Z' {
        let r0: char = (((c as u8) - ('A' as u8)) + ('a' as u8)) as char;
        r0
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
    let n: usize = s.len();
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            s@.len() == n as int,
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == #[trigger] flip_char(#[trigger] s@[j]),
        decreases (n as int) - (i as int)
    {
        let c = s[i];
        let r = exec_flip_char(c);
        result.push(r);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}