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
/* helper modified by LLM (iteration 5): Added an exec function for `to_toggle_case_spec` */
fn to_toggle_case_exec(s: char) -> (result: char)
    ensures result == to_toggle_case_spec(s)
{
    if s >= 'a' && s <= 'z' {
        ((s as u8) - 32) as char
    } else if s >= 'A' && s <= 'Z' {
        ((s as u8) + 32) as char
    } else {
        s
    }
}
// </vc-helpers>

// <vc-spec>
fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)

    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the `to_toggle_case_exec` function call by defining it in helpers and ensuring its correctness */
{
    let mut toggle_case = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant 
            0 <= i <= str1.len(),
            toggle_case.len() == i,
            forall|j: int| 0 <= j < i ==> toggle_case@[j] == to_toggle_case_spec(str1[j]),
        decreases str1.len() - i
    {
        let char_at_i = str1[i];
        let toggled_char = to_toggle_case_exec(char_at_i);
        
        toggle_case.push(toggled_char);
        i = i + 1;
    }
    toggle_case
}
// </vc-code>

}
fn main() {}