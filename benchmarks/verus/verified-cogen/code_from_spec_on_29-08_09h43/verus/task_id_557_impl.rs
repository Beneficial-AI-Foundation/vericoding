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
spec fn to_toggle_case_char(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else if is_upper_case(c) {
        shift32_spec(c)
    } else {
        c
    }
}

proof fn toggle_case_char_equiv(c: char)
    ensures to_toggle_case_char(c) == to_toggle_case_spec(c)
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause for loop termination */
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == to_toggle_case_spec(str1@[j]),
        decreases str1.len() - i,
    {
        let c = str1[i];
        let toggled_char = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        result.push(toggled_char);
        i = i + 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}