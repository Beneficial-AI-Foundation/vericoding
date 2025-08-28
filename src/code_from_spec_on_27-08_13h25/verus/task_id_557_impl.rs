use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end
// pure-end

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn to_toggle_case_spec(s: char) -> (result:char) {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}
// pure-end

// <vc-helpers>
// No updates needed in helpers for this specific error as the issue is with the loop decreases clause.
// </vc-helpers>

// <vc-spec>
fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut toggle_case: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < str1.len()
        invariant
            i <= str1.len(),
            toggle_case@.len() == i,
            forall|k: int| 0 <= k < i ==> toggle_case[k] == to_toggle_case_spec(#[trigger] str1[k]),
        decreases str1.len() - i
    {
        let c = str1[i];
        let toggled = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        toggle_case.push(toggled);
        i = i + 1;
    }
    
    toggle_case
}
// </vc-code>

} // verus!

fn main() {}