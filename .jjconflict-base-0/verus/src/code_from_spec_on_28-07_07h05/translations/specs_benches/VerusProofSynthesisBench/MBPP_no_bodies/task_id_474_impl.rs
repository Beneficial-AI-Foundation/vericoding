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
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str1.len()
        invariant
            idx <= str1.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
        decreases str1.len() - idx,
    {
        let char_to_add = if str1[idx] == old_char {
            new_char
        } else {
            str1[idx]
        };
        result.push(char_to_add);
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}