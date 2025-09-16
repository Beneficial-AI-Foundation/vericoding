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
/* helper modified by LLM (iteration 4): executable helper to flip a single character consistent with flip_case_spec */
fn flip_case_char(c: char) -> (r: char)
    ensures
        r == flip_case_spec(c),
{
    if c >= 'a' && c <= 'z' {
        (((c as u8) - 32) as char)
    } else if c >= 'A' && c <= 'Z' {
        (((c as u8) + 32) as char)
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
{
    /* code modified by LLM (iteration 4): iterative traversal with loop invariants and safe indexing and seq push facts */
    let n = str.len();
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            (out@).len() == i as int,
            0 <= i as int <= n as int,
            n as int == (str@).len(),
            forall|j: int| 0 <= j < i as int ==> out@[j] == flip_case_spec(#[trigger] str[j]),
        decreases n as int - i as int
    {
        let c = str[i];
        let r = flip_case_char(c);
        out.push(r);
        assert(r == flip_case_spec(#[trigger] str[i as int]));
        assert(out@[(i as int)] == r);
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}