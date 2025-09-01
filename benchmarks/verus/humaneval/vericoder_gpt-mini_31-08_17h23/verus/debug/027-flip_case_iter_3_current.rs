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
// Updated helpers: no additional lemmas required for this implementation.
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
    // impl-start
    let n: nat = str.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n,
        invariant res@.len() == i,
        invariant forall|j: nat| j < i ==> res@[j] == flip_case_spec(#[trigger] str@[j]),
    {
        let c: char = str[i as usize];
        let cu: u8 = c as u8;
        let fc: char;
        if c >= 'a' && c <= 'z' {
            fc = ((cu - 32) as char);
            proof {
                assert(cu == (c as u8));
                assert(fc == ((c as u8 - 32) as char));
                assert(is_lower_case(#[trigger] c) == (c >= 'a' && c <= 'z'));
                assert(is_lower_case(c));
                assert(flip_case_spec(c) == shift_minus_32_spec(c));
                assert(fc == flip_case_spec(c));
            }
        } else if c >= 'A' && c <= 'Z' {
            fc = ((cu + 32) as char);
            proof {
                assert(cu == (c as u8));
                assert(fc == ((c as u8 + 32) as char));
                assert(is_upper_case(#[trigger] c) == (c >= 'A' && c <= 'Z'));
                assert(is_upper_case(c));
                assert(flip_case_spec(c) == shift_plus_32_spec(c));
                assert(fc == flip_case_spec(c));
            }
        } else {
            fc = c;
            proof {
                assert(!(c >= 'a' && c <= 'z'));
                assert(!(c >= 'A' && c <= 'Z'));
                assert(is_lower_case(#[trigger] c) == (c >= 'a' && c <= 'z'));
                assert(is_upper_case(#[trigger] c) == (c >= 'A' && c <= 'Z'));
                assert(!is_lower_case(c));
                assert(!is_upper_case(c));
                assert(flip_case_spec(c) == c);
                assert(fc == flip_case_spec(c));
            }
        }
        proof {
            assert(fc == flip_case_spec(#[trigger] c));
            assert(forall|j: nat| j < i ==> res@[j] == flip_case_spec(#[trigger] str@[j]));
        }
        res.push(fc);
        i = i + 1;
    }
    res
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}