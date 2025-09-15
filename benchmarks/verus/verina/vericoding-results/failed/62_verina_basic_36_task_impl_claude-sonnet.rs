// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): string construction helpers using correct Verus string API */
fn string_from_char(c: char) -> (result: String)
    ensures result@.len() == 1, result@.index(0) == c
{
    let mut s = String::new();
    s.push(c);
    s
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
    /* code modified by LLM (iteration 5): fixed syntax error in sequence length access */
    let mut result = String::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@.index(j) == if is_space_comma_dot(s@.index(j)) { ':' } else { s@.index(j) }
    {
        proof {
            assert(i < s.len());
            assert(0 <= i as int && i as int < s@.len());
        }
        let c = s.as_bytes()[i] as char;
        proof {
            assert(c == s@.index(i as int));
        }
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}