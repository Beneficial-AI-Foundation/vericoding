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
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == inner_expr_replace_blanks_with_chars(str1, ch, j),
        decreases str1.len() - i
    {
        let current_char = str1[i];
        if current_char == ' ' {
            result.push(ch);
        } else {
            result.push(current_char);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}