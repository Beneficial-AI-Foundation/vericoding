// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}

spec fn shift_plus_32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}

spec fn flip_case_spec(c: char) -> (result:char) {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else if is_upper_case(c) {
        shift_plus_32_spec(c)
    } else {
        c
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed preconditions that cannot be satisfied for all characters */
fn flip_case_char(c: char) -> (result: char)
    ensures
        result == flip_case_spec(c),
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
fn flip_case(str: &[char]) -> (flipped_case: Vec<char>)

    ensures
        str@.len() == flipped_case@.len(),
        forall|i: int| 0 <= i < str.len() ==> flipped_case[i] == flip_case_spec(#[trigger] str[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement flip_case logic directly without helper function */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == flip_case_spec(str[j]),
        decreases str.len() - i
    {
        let c = str[i];
        let flipped = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        result.push(flipped);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}