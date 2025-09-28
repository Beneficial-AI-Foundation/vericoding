// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change needed, helper function is correct. */
fn is_space_comma_dot_exec(c: char) -> (b: bool)
    ensures
        b == is_space_comma_dot(c),
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected the function name from string_from_seq to String::from_seq to fix compilation error. */
    let mut result_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < s.len_chars()
        invariant
            i <= s.len_chars(),
            result_vec@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> {
                if is_space_comma_dot(s@[j]) {
                    result_vec@[j] == ':'
                } else {
                    result_vec@[j] == s@[j]
                }
            },
        decreases s.len_chars() - i
    {
        let c = s.get_char(i);
        if is_space_comma_dot_exec(c) {
            result_vec.push(':');
        } else {
            result_vec.push(c);
        }
        i = i + 1;
    }

    let result_string = String::from_seq(result_vec@);
    result_string
}
// </vc-code>

}
fn main() {}