// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn inner_epxr_replace_chars(str1: &Vec<char>, old_char: char, new_char: char, i: int) -> (result: char) {
    if str1[i] == old_char {
        new_char
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace_chars(str1: &Vec<char>, old_char: char, new_char: char) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}