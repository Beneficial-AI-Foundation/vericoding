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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (if is_upper_case(#[trigger] str1[j]) { shift32_spec(str1[j]) } else { str1[j] })
        decreases str1.len() - i
    {
        let c = str1[i];
        if c >= 'A' && c <= 'Z' {
            let new_c = ((c as u8) + 32) as char;
            result.push(new_c);
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}