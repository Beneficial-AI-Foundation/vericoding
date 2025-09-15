// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn inner_expr_replace_blanks_with_chars(str1: &Vec<char>, ch: char, i: int) -> (result: char) {
    if str1[i] == 32 {
        ch
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_blanks_with_chars(str1: &Vec<char>, ch: char) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}