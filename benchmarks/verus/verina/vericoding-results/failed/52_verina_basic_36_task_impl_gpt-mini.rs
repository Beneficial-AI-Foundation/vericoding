// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
spec fn id_char(c: char) -> char { c }
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
    let mut result = String::new();
    let mut i: int = 0;
    let cs_len_usize = s.chars().count();
    let n: int = cs_len_usize as int;
    while i < n
        invariant
            0 <= i,
            i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result@.index(j) == if is_space_comma_dot(#[trigger] s@.index(j)) { ':' } else { s@.index(j) },
        decreases n - i
    {
        let ch = s.chars().nth(i as usize).unwrap();
        if is_space_comma_dot(ch) {
            result.push(':');
        } else {
            result.push(ch);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}