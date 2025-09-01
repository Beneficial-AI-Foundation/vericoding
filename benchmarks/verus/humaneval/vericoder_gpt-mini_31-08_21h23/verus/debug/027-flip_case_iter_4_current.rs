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
// no helpers needed
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
    let mut res: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < str.len()
        invariant i <= str.len();
        invariant res@.len() == i;
        invariant forall|k: nat| k < i ==> res@[k] == flip_case_spec(#[trigger] str[k]);
        decreases str.len() - i;
    {
        let c: char = str[i];
        let newc: char =
            if is_lower_case(c) {
                ((c as u8) - 32) as char
            } else if is_upper_case(c) {
                ((c as u8) + 32) as char
            } else {
                c
            };
        proof {
            if is_lower_case(c) {
                assert(flip_case_spec(#[trigger] c) == shift_minus_32_spec(c));
                assert(shift_minus_32_spec(c) == ((c as u8) - 32) as char);
            } else if is_upper_case(c) {
                assert(flip_case_spec(#[trigger] c) == shift_plus_32_spec(c));
                assert(shift_plus_32_spec(c) == ((c as u8) + 32) as char);
            } else {
                assert(flip_case_spec(#[trigger] c) == c);
            }
            assert(newc == flip_case_spec(#[trigger] c));
        }
        res.push(newc);
        i += 1;
    }
    res
}
// </vc-code>

} // verus!
fn main() {}