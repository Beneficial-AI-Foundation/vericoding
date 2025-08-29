use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}

// <vc-helpers>
fn shift_minus_32(c: char) -> (result: char)
    requires c >= 'a' && c <= 'z'
    ensures result == shift_minus_32_spec(c)
{
    ((c as u8) - 32) as char
}

fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_to_uppercase(str1, j),
        decreases str1.len() - i
    {
        let c = str1[i];
        /* code modified by LLM (iteration 2): replaced is_lower_case with is_lower_case_exec */
        if is_lower_case_exec(c) {
            result.push(shift_minus_32(c));
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}