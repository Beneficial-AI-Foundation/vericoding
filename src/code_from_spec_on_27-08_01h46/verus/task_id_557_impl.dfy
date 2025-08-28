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
proof fn lemma_char_bounds(c: char)
    requires c as u8 <= 127
    ensures
        c >= 'A' && c <= 'Z' ==> (c as u8) >= 65 && (c as u8) <= 90,
        c >= 'a' && c <= 'z' ==> (c as u8) >= 97 && (c as u8) <= 122,
        c >= 'A' && c <= 'Z' ==> ((c as u8) + 32) >= 97 && ((c as u8) + 32) <= 122,
        c >= 'a' && c <= 'z' ==> ((c as u8) - 32) >= 65 && ((c as u8) - 32) <= 90,
{
}

fn to_upper_char(c: char) -> (result: char)
    requires is_lower_case(c) && c as u8 <= 127
    ensures result == shift_minus_32_spec(c)
{
    proof { lemma_char_bounds(c); }
    ((c as u8) - 32) as char
}

fn to_lower_char(c: char) -> (result: char)
    requires is_upper_case(c) && c as u8 <= 127
    ensures result == shift32_spec(c)
{
    proof { lemma_char_bounds(c); }
    ((c as u8) + 32) as char
}

exec fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}

exec fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
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
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == to_toggle_case_spec(#[trigger] str1[j]),
        decreases str1.len() - i
    {
        let c = str1[i];
        let toggled = if is_lower_case_exec(c) && c as u8 <= 127 {
            to_upper_char(c)
        } else if is_upper_case_exec(c) && c as u8 <= 127 {
            to_lower_char(c)
        } else {
            c
        };
        result.push(toggled);
        i = i + 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}