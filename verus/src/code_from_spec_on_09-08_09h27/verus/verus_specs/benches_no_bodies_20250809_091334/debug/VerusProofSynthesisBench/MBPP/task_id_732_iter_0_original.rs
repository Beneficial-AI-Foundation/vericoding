use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot_spec(c: char) -> (result: bool) {
    (c == ' ') || (c == ',') || (c == '.')
}
// pure-end

spec fn inner_expr_replace_with_colon(str1: &Vec<char>, k: int) -> (result: char) {
    if is_space_comma_dot_spec(str1[k]) {
        ':'
    } else {
        str1[k]
    }
}
// pure-end

fn replace_with_colon(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|k: int|
            0 <= k < result.len() ==> #[trigger] result[k] == inner_expr_replace_with_colon(str1, k),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
