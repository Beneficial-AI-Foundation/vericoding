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
/* helper modified by LLM (iteration 4): fixed exec mode issue by making helper functions exec instead of spec */
fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}

fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}

fn to_upper_case(c: char) -> (result: char)
    requires is_lower_case(c)
    ensures result == shift_minus_32_spec(c)
{
    ((c as u8) - 32) as char
}

fn to_lower_case(c: char) -> (result: char)
    requires is_upper_case(c)
    ensures result == shift32_spec(c)
{
    ((c as u8) + 32) as char
}

fn toggle_char(c: char) -> (result: char)
    ensures result == to_toggle_case_spec(c)
{
    if is_lower_case_exec(c) {
        to_upper_case(c)
    } else if is_upper_case_exec(c) {
        to_lower_case(c)
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
/* code modified by LLM (iteration 4): added decreases clause to while loop */
{
    let mut toggle_case = Vec::new();
    let mut i = 0;
    
    while i < str1.len()
        invariant
            i <= str1.len(),
            toggle_case.len() == i,
            forall|j: int| 0 <= j < i ==> toggle_case[j] == to_toggle_case_spec(str1[j]),
        decreases str1.len() - i
    {
        let toggled_char = toggle_char(str1[i]);
        toggle_case.push(toggled_char);
        i = i + 1;
    }
    
    toggle_case
}
// </vc-code>

}
fn main() {}