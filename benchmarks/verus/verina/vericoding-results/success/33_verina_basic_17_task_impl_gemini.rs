// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn shift32(c: char) -> char {
    ((c as int) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [avoid unsupported char::from_u32 by using u8 conversion] */
fn char_to_lowercase(c: char) -> (result: char)
    ensures
        if is_uppercase(c) { result == shift32(c) } else { result == c }
{
    if 'A' <= c && c <= 'Z' {
        (c as u8 + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn to_lowercase(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if is_uppercase(s[i]) {
                result[i] == shift32(s[i])
            } else {
                result[i] == s[i]
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [no logic change, only helper fix was needed] */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> {
                if is_uppercase(s[j]) {
                    result[j] == shift32(s[j])
                } else {
                    result[j] == s[j]
                }
            },
        decreases s.len() - i
    {
        let c = s[i];
        let lower_c = char_to_lowercase(c);
        result.push(lower_c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}