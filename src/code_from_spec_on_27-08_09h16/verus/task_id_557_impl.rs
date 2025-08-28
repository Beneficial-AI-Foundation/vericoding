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
fn shift32(c: char) -> (result: char)
    requires c >= 'A' && c <= 'Z'
    ensures result == shift32_spec(c)
{
    ((c as u8) + 32) as char
}

fn shift_minus_32(c: char) -> (result: char)
    requires c >= 'a' && c <= 'z'
    ensures result == shift_minus_32_spec(c)
{
    ((c as u8) - 32) as char
}

fn to_toggle_case_char(c: char) -> (result: char)
    ensures result == to_toggle_case_spec(c)
{
    if is_lower_case(c) {
        shift_minus_32(c)
    } else if is_upper_case(c) {
        shift32(c)
    } else {
        c
    }
}
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
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == to_toggle_case_spec(str1@[j])
    {
        let toggled_char = to_toggle_case_char(str1[i]);
        result.push(toggled_char);
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}