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
#[verifier(external_body)]
#[cfg(test)]
pub fn char_to_u8(c: char) -> u8 {
    c as u8
}

#[verifier(external_body)]
#[cfg(test)]
pub fn u8_to_char(n: u8) -> char {
    n as char
}
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
    let mut flipped_vec: Vec<char> = Vec::new();
    let mut i: int = 0;

    while i < str.len()
        invariant
            0 <= i <= str.len(),
            flipped_vec@.len() == i,
            forall|j: int| 0 <= j < i ==> flipped_vec@[j] == flip_case_spec(#[trigger] str@[j]),
    {
        let c = str[i];
        let flipped_c: char;

        if is_lower_case(c) {
            flipped_c = (char_to_u8(c) - 32) as char;
            proof {
                assert(flipped_c == shift_minus_32_spec(c));
                assert(flipped_c == flip_case_spec(c));
            }
        } else if is_upper_case(c) {
            flipped_c = (char_to_u8(c) + 32) as char;
            proof {
                assert(flipped_c == shift_plus_32_spec(c));
                assert(flipped_c == flip_case_spec(c));
            }
        } else {
            flipped_c = c;
            proof {
                assert(flipped_c == flip_case_spec(c));
            }
        }
        flipped_vec.push(flipped_c);
        i = i + 1;
    }

    assert(flipped_vec.len() == str.len());
    assert(forall|k: int| 0 <= k < str.len() ==> flipped_vec@[k] == flip_case_spec(#[trigger] str@[k]));
    flipped_vec
}
// </vc-code>

} // verus!
fn main() {}