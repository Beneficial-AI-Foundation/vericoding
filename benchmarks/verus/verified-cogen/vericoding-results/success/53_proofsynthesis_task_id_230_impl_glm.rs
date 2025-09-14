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
/* code modified by LLM (iteration 4): removed duplicate helper function definition */
{
    let mut result = Vec::<char>::new();
    let n = str1.len();
    
    for i in 0..n
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_replace_blanks_with_chars(str1, ch, j),
            n == str1.len()
    {
        let current_char = str1[i];
        let new_char = if current_char == ' ' { ch } else { current_char };
        result.push(new_char);
    }
    
    result
}
// </vc-code>

}
fn main() {}