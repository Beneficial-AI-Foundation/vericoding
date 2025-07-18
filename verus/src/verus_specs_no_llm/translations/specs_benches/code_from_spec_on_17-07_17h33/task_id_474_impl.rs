use vstd::prelude::*;

verus! {

spec fn inner_epxr_replace_chars(str1: &Vec<char>, old_char: char, new_char: char, i: int) -> (result: char) {
    if str1[i] == old_char {
        new_char
    } else {
        str1[i]
    }
}
// pure-end

fn replace_chars(str1: &Vec<char>, old_char: char, new_char: char) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1@.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
{
    /* code modified by LLM (iteration 1): Fixed compilation errors - moved ensures clause to correct position, removed incorrect return statement, implemented proper function body */
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 2): Added decreases clause to fix compilation error */
    while idx < str1.len()
        invariant
            0 <= idx <= str1@.len(),
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
        decreases str1@.len() - idx
    {
        let ch = str1[idx];
        if ch == old_char {
            result.push(new_char);
        } else {
            result.push(ch);
        }
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}