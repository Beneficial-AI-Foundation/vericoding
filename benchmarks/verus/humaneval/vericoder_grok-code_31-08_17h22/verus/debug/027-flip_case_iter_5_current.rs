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
// No updates needed in helpers for this implementation
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
    let mut result: Vec<char> = Vec::with_capacity(str.len());
    let mut i = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == flip_case_spec(#[trigger] str[j])
    {
        let c = str[i];
        let flipped = if (c >= 'a' && c <= 'z') {
            ((c as u8) - 32) as char
        } else if (c >= 'A' && c <= 'Z') {
            ((c as u8) + 32) as char
        } else {
            c
        };
        assert(flipped == flip_case_spec(c));
        result.push(flipped);
        i += 1;
    }
    result
}
// </vc-code>

} // verus!
fn main() {}