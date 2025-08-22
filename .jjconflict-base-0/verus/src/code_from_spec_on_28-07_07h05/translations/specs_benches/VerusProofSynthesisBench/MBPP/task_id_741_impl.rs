use vstd::prelude::*;

verus! {

//IMPL all_characters_same
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
    /* code modified by LLM (iteration 1): changed idx type to int to fix type mismatch */
    let mut idx: int = 1;
    
    /* code modified by LLM (iteration 1): fixed loop invariant and added assertion for postcondition */
    while idx < char_arr@.len()
        invariant
            1 <= idx <= char_arr@.len(),
            forall|i: int| 1 <= i < idx ==> char_arr[0] == #[trigger] char_arr[i],
        decreases char_arr@.len() - idx,
    {
        if char_arr[idx] != first_char {
            /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning false */
            assert(char_arr[0] != char_arr[idx]);
            assert(1 <= idx < char_arr@.len());
            assert(exists|i: int| 1 <= i < char_arr@.len() && char_arr[0] != char_arr[i]);
            return false;
        }
        /* code modified by LLM (iteration 1): added assertion to maintain loop invariant */
        assert(char_arr[0] == char_arr[idx]);
        idx = idx + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning true */
    assert(idx == char_arr@.len());
    assert(forall|i: int| 1 <= i < char_arr@.len() ==> char_arr[0] == char_arr[i]);
    return true;
}

} // verus!

fn main() {}