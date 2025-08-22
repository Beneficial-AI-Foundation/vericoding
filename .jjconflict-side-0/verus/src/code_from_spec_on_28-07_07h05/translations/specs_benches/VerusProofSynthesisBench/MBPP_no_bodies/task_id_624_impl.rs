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

/* code modified by LLM (iteration 1): Added executable version of is_lower_case for use in implementation */
fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}

fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while idx < str1.len()
        invariant
            idx <= str1.len(),
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == inner_expr_to_uppercase(str1, i),
        decreases str1.len() - idx
    {
        let c = str1[idx];
        /* code modified by LLM (iteration 1): Changed from is_lower_case(c) to is_lower_case_exec(c) to use executable function */
        if is_lower_case_exec(c) {
            let upper_c = ((c as u8) - 32) as char;
            result.push(upper_c);
        } else {
            result.push(c);
        }
        idx = idx + 1;
    }
    
    result
}

} // verus!

fn main() {}