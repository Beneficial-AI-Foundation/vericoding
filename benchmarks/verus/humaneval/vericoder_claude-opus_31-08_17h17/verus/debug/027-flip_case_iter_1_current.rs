use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_plus_32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn flip_case_spec(c: char) -> (result:char) {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else if is_upper_case(c) {
        shift_plus_32_spec(c)
    } else {
        c
    }
}
// pure-end

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn flip_case(str: &[char]) -> (flipped_case: Vec<char>)
    // post-conditions-start
    ensures
        str@.len() == flipped_case@.len(),
        forall|i: int| 0 <= i < str.len() ==> flipped_case[i] == flip_case_spec(#[trigger] str[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == flip_case_spec(#[trigger] str[j]),
    {
        let c = str[i];
        let flipped = if c >= 'a' && c <= 'z' {
            // Convert lowercase to uppercase
            let c_u8 = c as u8;
            let flipped_u8 = c_u8 - 32;
            flipped_u8 as char
        } else if c >= 'A' && c <= 'Z' {
            // Convert uppercase to lowercase
            let c_u8 = c as u8;
            let flipped_u8 = c_u8 + 32;
            flipped_u8 as char
        } else {
            c
        };
        
        assert(flipped == flip_case_spec(c)) by {
            if c >= 'a' && c <= 'z' {
                assert(is_lower_case(c));
                assert(flipped == shift_minus_32_spec(c));
            } else if c >= 'A' && c <= 'Z' {
                assert(is_upper_case(c));
                assert(flipped == shift_plus_32_spec(c));
            } else {
                assert(!is_lower_case(c));
                assert(!is_upper_case(c));
            }
        }
        
        result.push(flipped);
        i = i + 1;
    }
    
    result
}
// </vc-code>

} // verus!
fn main() {}