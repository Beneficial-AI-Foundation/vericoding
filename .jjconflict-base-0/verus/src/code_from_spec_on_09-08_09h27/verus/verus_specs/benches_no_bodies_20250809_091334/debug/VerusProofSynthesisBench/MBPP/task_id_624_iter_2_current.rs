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

fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < str1.len()
        invariant
            result@.len() == index,
            forall|i: int| 0 <= i < index ==> result[i] == inner_expr_to_uppercase(str1, i),
    {
        let c = str1[index];
        /* code modified by LLM (iteration 1): replaced spec function call with executable condition */
        if c >= 'a' && c <= 'z' {
            let uppercase_c = ((c as u8) - 32) as char;
            result.push(uppercase_c);
            /* code modified by LLM (iteration 1): added proof block to establish postcondition */
            proof {
                assert(is_lower_case(c));
                assert(uppercase_c == shift_minus_32_spec(c));
                assert(result[index as int] == inner_expr_to_uppercase(str1, index as int));
            }
        } else {
            result.push(c);
            /* code modified by LLM (iteration 1): added proof block to establish postcondition */
            proof {
                assert(!is_lower_case(c));
                assert(result[index as int] == inner_expr_to_uppercase(str1, index as int));
            }
        }
        index += 1;
    }
    
    result
}

} // verus!

fn main() {}