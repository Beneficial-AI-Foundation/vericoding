// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed to_seq compilation error */fn replace_chars_in_string(s: &str) -> (result: String)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> 
            #[trigger] result@.index(i) == 
            if is_space_comma_dot(#[trigger] s@.index(i)) { ':' } else { s@.index(i) }
{
    let mut result_chars: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            result_chars@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result_chars@.index(j) == 
                if is_space_comma_dot(#[trigger] s@.index(j)) { ':' } else { s@.index(j) }
    {
        let c = s@[i];
        if is_space_comma_dot(c) {
            result_chars.push(':');
        } else {
            result_chars.push(c);
        }
        i = i + 1;
    }
    String::from_iter(result_chars)
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
{
    /* code modified by LLM (iteration 4): fixed compilation error by avoiding to_seq */
    let mut result_chars: Vec<char> = Vec::new();
    let mut i = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            result_chars@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result_chars@.index(j) == 
                if is_space_comma_dot(#[trigger] s@.index(j)) { ':' } else { s@.index(j) }
    {
        let c = s@[i];
        if is_space_comma_dot(c) {
            result_chars.push(':');
        } else {
            result_chars.push(c);
        }
        i = i + 1;
    }
    String::from_iter(result_chars)
}
// </vc-code>

}
fn main() {}