use vstd::prelude::*;

verus! {

spec fn inner_expr_replace_blanks_with_chars(str1: &Vec<char>, ch: char, i: int) -> (result: char) {
    if str1[i] == 32 {
        ch
    } else {
        str1[i]
    }
}
// pure-end

fn replace_blanks_with_chars(str1: &Vec<char>, ch: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
