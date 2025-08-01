use vstd::prelude::*;

verus! {

spec fn inner_expr_replace_blanks_with_chars(str1: &Vec<char>, ch: char, i: int) -> (result: char) {
    /* code modified by LLM (iteration 1): changed 32 to ' ' for proper char comparison */
    if str1[i] == ' ' {
        ch
    } else {
        str1[i]
    }
}
// pure-end

fn replace_blanks_with_chars(str1: &Vec<char>, ch: char) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 2): added decreases clause to prove termination */
    while idx < str1.len()
        invariant
            0 <= idx <= str1.len(),
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
        decreases str1.len() - idx,
    {
        /* code modified by LLM (iteration 1): changed 32 to ' ' for proper char comparison */
        if str1[idx] == ' ' {
            result.push(ch);
        } else {
            result.push(str1[idx]);
        }
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}