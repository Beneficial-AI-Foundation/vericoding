// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No functional changes needed. */
fn to_uppercase_char(c: char) -> (result: char)
    ensures result == if is_lower_case(c) { shift_minus_32_spec(c) } else { c }
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Changed loop counter from ghost 'int' to executable 'usize' to fix compilation. */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            0 <= i as int,
            i as int <= str1.len() as int,
            result.view().len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == inner_expr_to_uppercase(str1, j),
        decreases str1.len() - i
    {
        let c = str1[i];
        let upper_c = to_uppercase_char(c);
        result.push(upper_c);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}