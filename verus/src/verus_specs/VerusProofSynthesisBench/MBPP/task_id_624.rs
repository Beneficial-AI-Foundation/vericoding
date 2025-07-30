use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}
// pure-end

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}

fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}

