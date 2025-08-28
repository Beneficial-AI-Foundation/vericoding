use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}

// <vc-helpers>
spec fn char_is_valid_ascii(c: char) -> bool {
    c as u32 <= 127
}

proof fn shift_char_preserves_validity(c: char)
    requires 
        char_is_valid_ascii(c),
        is_lower_case(c)
    ensures 
        char_is_valid_ascii(shift_minus_32_spec(c))
{
    assert(c >= 'a' && c <= 'z');
    assert(c as u8 >= 97u8 && c as u8 <= 122u8);
    assert((c as u8) - 32 >= 65u8 && (c as u8) - 32 <= 90u8);
}

fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    
    for i in 0..str1.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_to_uppercase(str1, j)
    {
        let c = str1[i];
        if is_lower_case_exec(c) {
            let upper_c = ((c as u8) - 32) as char;
            result.push(upper_c);
        } else {
            result.push(c);
        }
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}