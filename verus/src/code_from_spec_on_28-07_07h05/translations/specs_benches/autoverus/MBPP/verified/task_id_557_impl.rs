use vstd::prelude::*;
fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

spec fn is_lower_case(c: u8) -> bool {
    c >= 97 && c <= 122
}

spec fn shift_minus_32_spec(c: u8) -> u8 {
    (c - 32) as u8
}

spec fn to_toggle_case_spec(s: u8) -> u8 {
    if is_lower_case(s) {
        shift_minus_32_spec(s)
    } else if is_upper_case(s) {
        shift32_spec(s)
    } else {
        s
    }
}

fn to_toggle_case(str1: &[u8]) -> (toggle_case: Vec<u8>)
    ensures
        str1@.len() == toggle_case@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> toggle_case[i] == to_toggle_case_spec(#[trigger] str1[i]),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str1.len()
        invariant
            0 <= idx <= str1.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == to_toggle_case_spec(str1[i]),
        decreases str1.len() - idx,
    {
        let c = str1[idx];
        let toggled = if c >= 97 && c <= 122 {
            // lowercase to uppercase
            c - 32
        } else if c >= 65 && c <= 90 {
            // uppercase to lowercase  
            c + 32
        } else {
            // leave unchanged
            c
        };
        
        result.push(toggled);
        idx += 1;
    }
    
    result
}

} // verus!