// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): executable predicate mirrors spec exactly */
fn is_upper_case_exec(c: char) -> (ret: bool)
    ensures
        ret == is_upper_case(c)
{
    c >= 'A' && c <= 'Z'
}

/* helper modified by LLM (iteration 4): executable shift using casts; equals spec */
fn shift32_exec(c: char) -> (ret: char)
    requires
        is_upper_case(c)
    ensures
        ret == shift32_spec(c)
{
    let u: u8 = c as u8;
    let shifted: u8 = u + 32;
    let r: char = shifted as char;
    r
}
// </vc-helpers>

// <vc-spec>
fn to_lowercase(str1: &Vec<char>) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate and map each char to lowercase using helpers; maintain prefix invariant */
    let n = str1.len();
    let mut result_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            str1.len() == n,
            str1@.len() == n as int,
            result_vec@.len() == i as int,
            forall|j: int|
                0 <= j < i as int ==> result_vec@[j] == (if is_upper_case(str1@[j]) { shift32_spec(str1@[j]) } else { str1@[j] })
        decreases n - i
    {
        let c = str1[i];
        let is_up = is_upper_case_exec(c);
        proof { assert(is_up == is_upper_case(c)); }
        let r = if is_up { shift32_exec(c) } else { c };
        result_vec.push(r);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}