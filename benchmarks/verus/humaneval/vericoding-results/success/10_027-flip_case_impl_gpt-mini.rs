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
/* helper modified by LLM (iteration 5): relate flip_case_spec to its case expression */
proof fn flip_case_eq_spec(c: char) ensures flip_case_spec(c) == if is_lower_case(c) { shift_minus_32_spec(c) } else if is_upper_case(c) { shift_plus_32_spec(c) } else { c } {
    if is_lower_case(c) {
        assert(flip_case_spec(c) == shift_minus_32_spec(c));
    } else if is_upper_case(c) {
        assert(flip_case_spec(c) == shift_plus_32_spec(c));
    } else {
        assert(flip_case_spec(c) == c);
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
    /* code modified by LLM (iteration 5): iterate and build flipped vector with invariants ensuring length and mapping */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            res@.len() == i as int,
            i <= str.len(),
            forall|j: int| 0 <= j < i as int ==> res@[j] == flip_case_spec(#[trigger] str@[j]),
        decreases str.len() - i
    {
        let c: char = str[i];
        let fc: char = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        res.push(fc);
        i = i + 1;
    }
    proof {
        assert(i == str.len());
        assert(res@.len() == i as int);
        assert(res@.len() == str@.len());
    }
    res
}
// </vc-code>

}
fn main() {}