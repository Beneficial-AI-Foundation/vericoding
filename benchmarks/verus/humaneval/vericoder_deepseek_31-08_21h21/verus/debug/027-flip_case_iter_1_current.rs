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
proof fn shift_plus_32_upper_case(c: char)
    requires
        is_upper_case(c),
    ensures
        shift_plus_32_spec(c) as u8 == (c as u8) + 32,
        is_lower_case(shift_plus_32_spec(c)),
{
}

proof fn shift_minus_32_lower_case(c: char)
    requires
        is_lower_case(c),
    ensures
        shift_minus_32_spec(c) as u8 == (c as u8) - 32,
        is_upper_case(shift_minus_32_spec(c)),
{
}

proof fn flip_case_properties(c: char)
    ensures
        flip_case_spec(c) == {
            if is_lower_case(c) {
                ((c as u8) - 32) as char
            } else if is_upper_case(c) {
                ((c as u8) + 32) as char
            } else {
                c
            }
        },
{
    if is_lower_case(c) {
        shift_minus_32_lower_case(c);
    } else if is_upper_case(c) {
        shift_plus_32_upper_case(c);
    }
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
    let mut flipped_case = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            flipped_case@.len() == i,
            forall|j: int| 0 <= j < i ==> flipped_case@[j] == flip_case_spec(str[j]),
    {
        let c = str[i];
        let flipped_char = if is_lower_case(c) {
            ((c as u8) - 32) as char
        } else if is_upper_case(c) {
            ((c as u8) + 32) as char
        } else {
            c
        };
        flipped_case.push(flipped_char);
        proof {
            flip_case_properties(c);
        }
        assert(flipped_case@[i] == flip_case_spec(str[i]));
        i += 1;
    }
    flipped_case
}
// </vc-code>

} // verus!
fn main() {}