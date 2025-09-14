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
/* helper modified by LLM (iteration 2): no functional change */
fn toggle_char(c: char) -> (res: char)
    ensures res == to_toggle_case_spec(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else if c >= 'A' && c <= 'Z' {
        ((c as u8) + 32) as char
    } else {
        c
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
{
    /* code modified by LLM (iteration 2): added decreases clause to fix termination check */
    let mut toggle_case = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            toggle_case@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> toggle_case@[j] == to_toggle_case_spec(str1@[j]),
        decreases str1.len() - i
    {
        let c = str1[i];
        let toggled_c = toggle_char(c);
        toggle_case.push(toggled_c);
        i = i + 1;
    }
    toggle_case
}
// </vc-code>

}
fn main() {}