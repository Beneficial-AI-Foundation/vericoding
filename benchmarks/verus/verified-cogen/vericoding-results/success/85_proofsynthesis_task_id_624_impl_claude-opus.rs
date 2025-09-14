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
fn shift_minus_32(c: char) -> (result: char)
    requires is_lower_case(c)
    ensures result == shift_minus_32_spec(c)
{
    ((c as u8) - 32) as char
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
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_to_uppercase(str1, j)
        decreases str1.len() - i
    {
        let c = str1[i];
        if c >= 'a' && c <= 'z' {
            let shifted = shift_minus_32(c);
            result.push(shifted);
        } else {
            result.push(c);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}