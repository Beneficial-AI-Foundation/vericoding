// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot_spec(c: char) -> (result: bool) {
    (c == ' ') || (c == ',') || (c == '.')
}

spec fn inner_expr_replace_with_colon(str1: &Vec<char>, k: int) -> (result: char) {
    if is_space_comma_dot_spec(str1[k]) {
        ':'
    } else {
        str1[k]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): named the return value to fix compilation error */
fn is_space_comma_dot(c: char) -> (result: bool)
    ensures result == is_space_comma_dot_spec(c)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(str1: &Vec<char>) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == inner_expr_replace_with_colon(str1, k),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented loop with invariants to prove postconditions */
{
    let n = str1.len();
    let mut result = Vec::with_capacity(n);
    for i in 0..n
        invariant 
            n == str1.len(),
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k] == inner_expr_replace_with_colon(str1, k)
    {
        let c = str1[i];
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
    }
    result
}
// </vc-code>

}
fn main() {}