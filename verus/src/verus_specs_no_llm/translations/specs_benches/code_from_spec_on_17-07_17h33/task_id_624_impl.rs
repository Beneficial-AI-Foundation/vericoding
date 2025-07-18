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

/* code modified by LLM (iteration 1): added executable version of is_lower_case for use in function body */
fn is_lower_case_exec(c: char) -> (result: bool)
    ensures result == is_lower_case(c)
{
    c >= 'a' && c <= 'z'
}

fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    /* code modified by LLM (iteration 1): moved ensures clause to correct position before function body */
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
{
    /* code modified by LLM (iteration 1): implemented proper function body and used executable version of is_lower_case */
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == inner_expr_to_uppercase(str1, j),
        decreases str1.len() - i
    {
        let c = str1[i];
        if is_lower_case_exec(c) {
            let upper_c = ((c as u8) - 32) as char;
            result.push(upper_c);
        } else {
            result.push(c);
        }
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}