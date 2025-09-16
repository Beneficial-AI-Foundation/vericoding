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
/* helper modified by LLM (iteration 2): created exec versions of helpers to fix spec/exec call error */
fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c),
{
    c >= 'a' && c <= 'z'
}

/* helper modified by LLM (iteration 2): created exec versions of helpers to fix spec/exec call error */
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c),
{
    c >= 'A' && c <= 'Z'
}

/* helper modified by LLM (iteration 2): changed to call exec helpers instead of spec helpers */
fn flip_case_char(c: char) -> (result: char)
    ensures result == flip_case_spec(c),
{
    if is_lower_case_exec(c) {
        ((c as u8) - 32) as char
    } else if is_upper_case_exec(c) {
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
/* code modified by LLM (iteration 2): no changes needed, logic is sound assuming helpers are fixed */
{
    let mut flipped_case = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            flipped_case@.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> flipped_case[j] == flip_case_spec(#[trigger] str[j]),
        decreases str.len() - i
    {
        let c = str[i];
        let flipped_c = flip_case_char(c);
        flipped_case.push(flipped_c);
        i = i + 1;
    }
    flipped_case
}
// </vc-code>

}
fn main() {}