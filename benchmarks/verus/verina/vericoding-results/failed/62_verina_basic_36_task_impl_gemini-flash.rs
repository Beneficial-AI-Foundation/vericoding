// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed type of `i` in loop to `usize` and used `i as int` for sequence indexing. */
{
    let mut result_string: String = String::new();
    let s_seq = s.to_char_seq();

    let mut i: usize = 0;
    while i < s_seq.len()
        invariant
            0 <= i as int <= s_seq.len(),
            result_string@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> 
                #[trigger] result_string@.index(k) == 
                if is_space_comma_dot(#[trigger] s_seq.index(k)) { ':' } else { s_seq.index(k) },
    {
        let c = s_seq.index(i as int);
        if is_space_comma_dot(c) {
            result_string.push(':');
        } else {
            result_string.push(c);
        }
        i = i + (1 as usize);
    }
    result_string
}
// </vc-code>

}
fn main() {}