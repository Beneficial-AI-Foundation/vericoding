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
fn is_space_comma_dot(c: char) -> (result: bool)
    ensures result == is_space_comma_dot_spec(c)
{
    (c == ' ') || (c == ',') || (c == '.')
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
{
    /* code modified by LLM (iteration 2): Changed loop counter 'i' to usize to fix type errors and fixed invariant to use sequence indexing. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] result@[k] == inner_expr_replace_with_colon(str1, k),
        decreases str1.len() - i
    {
        let c = str1[i];
        if is_space_comma_dot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}