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
    /* code modified by LLM (iteration 3): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_replace_blanks_with_chars(str1, ch, j),
        decreases str1.len() - i
    {
        if str1[i] == ' ' {
            result.push(ch);
        } else {
            result.push(str1[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}