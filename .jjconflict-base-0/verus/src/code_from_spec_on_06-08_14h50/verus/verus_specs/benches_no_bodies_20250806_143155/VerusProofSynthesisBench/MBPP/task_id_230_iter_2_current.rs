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
    
    while idx < str1.len()
        invariant
            idx <= str1.len(),
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == inner_expr_replace_blanks_with_chars(str1, ch, i),
    {
        /* code modified by LLM (iteration 1): changed 32 to ' ' for proper char comparison */
        let new_char = if str1[idx] == ' ' {
            ch
        } else {
            str1[idx]
        };
        result.push(new_char);
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}