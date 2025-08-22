use vstd::prelude::*;


verus! {

fn all_characters_same(char_arr: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
    // post-conditions-end
{
    if char_arr.len() == 0 {
        return true;
    }
    
    let first_char = char_arr[0];
    
    for j in 1..char_arr.len()
        invariant
            /* code modified by LLM (iteration 1): Added trigger annotation to quantifier */
            forall|i: int| 1 <= i < j ==> char_arr[0] == #[trigger] char_arr[i]
    {
        if char_arr[j] != first_char {
            return false;
        }
    }
    
    true
}

} // verus!

fn main() {}