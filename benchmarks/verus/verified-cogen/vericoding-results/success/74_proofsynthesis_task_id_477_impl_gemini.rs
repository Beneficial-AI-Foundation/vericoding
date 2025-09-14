// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no change */
fn to_lower_char(c: char) -> (result: char)
    ensures
        result == if is_upper_case(c) { shift32_spec(c) } else { c },
{
    if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn to_lowercase(str1: &Vec<char>) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix termination check */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (if is_upper_case(#[trigger] str1[j]) {
                shift32_spec(str1[j])
            } else {
                str1[j]
            }),
        decreases str1.len() - i
    {
        let c = str1[i];
        let new_char = to_lower_char(c);
        result.push(new_char);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}