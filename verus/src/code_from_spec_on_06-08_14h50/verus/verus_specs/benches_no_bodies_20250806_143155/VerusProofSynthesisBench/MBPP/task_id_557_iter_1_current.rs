use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}
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

fn to_toggle_case(str1: &Vec<char>) -> (toggle_case: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < str1.len()
        invariant
            idx <= str1.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == to_toggle_case_spec(str1[i]),
    {
        let c = str1[idx];
        let toggled = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        
        result.push(toggled);
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}