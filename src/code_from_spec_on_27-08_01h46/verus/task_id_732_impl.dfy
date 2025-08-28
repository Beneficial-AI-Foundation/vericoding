use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot_spec(c: char) -> (result: bool) {
    (c == ' ') || (c == ',') || (c == '.')
}
// pure-end
// pure-end

spec fn inner_expr_replace_with_colon(str1: &Vec<char>, k: int) -> (result: char) {
    if is_space_comma_dot_spec(str1[k]) {
        ':'
    } else {
        str1[k]
    }
}
// pure-end

// <vc-helpers>
fn is_space_comma_dot(c: char) -> (result: bool)
    ensures result == is_space_comma_dot_spec(c)
{
    (c == ' ') || (c == ',') || (c == '.')
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == inner_expr_replace_with_colon(str1, k),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k] == inner_expr_replace_with_colon(str1, k)
        decreases str1.len() - i
    {
        let c = str1[i];
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

} // verus!

fn main() {}