// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
fn replace_char(c: char) -> char
{
    if is_space_comma_dot(c) { ':' } else { c }
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            #[trigger] result@.index(i) == 
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed String::new() to Ghost::new(). */
{
    let mut result_string: String = Ghost::new();
    let s_len = s.len(); // use `s.len()` directly
    let mut i: usize = 0;
    while i < s_len
        invariant 
            0 <= i as int <= s_len as int,
            result_string@.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result_string@.index(j) == #[trigger] replace_char(s@.index(j)),
        decreases s_len - i
    {
        let original_char: char = s.as_bytes()[i] as char; // Access character using `as_bytes()` and cast to char
        let new_char = replace_char(original_char);
        result_string.push(new_char);
        i = i + 1;
    }
    result_string
}
// </vc-code>

}
fn main() {}