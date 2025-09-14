// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}

spec fn to_toggle_case_spec(s: char) -> (result:char) {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause helper and kept exec helpers */
fn shift32(c: char) -> (result: char) requires is_upper_case(c), ensures result == shift32_spec(c) { ((c as u8) + 32) as char }
fn shift_minus_32(c: char) -> (result: char) requires is_lower_case(c), ensures result == shift_minus_32_spec(c) { ((c as u8) - 32) as char }
// </vc-helpers>

// <vc-spec>
fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)

    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clause to while loop */
{
    let mut toggle_case = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            toggle_case@.len() == i,
            forall|j: int| 0 <= j < i ==> toggle_case@[j] == to_toggle_case_spec(str1@[j])
        decreases str1.len() - i
    {
        let c = str1[i];
        let mut result_char = c;
        if c >= 'a' && c <= 'z' {
            proof { assert(is_lower_case(c)); }
            result_char = shift_minus_32(c);
        } else if c >= 'A' && c <= 'Z' {
            proof { assert(is_upper_case(c)); }
            result_char = shift32(c);
        }
        toggle_case.push(result_char);
        i += 1;
    }
    toggle_case
}
// </vc-code>

}
fn main() {}