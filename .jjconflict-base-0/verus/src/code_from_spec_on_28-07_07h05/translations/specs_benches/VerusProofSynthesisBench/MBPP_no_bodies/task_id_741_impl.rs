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
    /* code modified by LLM (iteration 2): changed idx to int type to match postcondition expectations */
    let mut idx: int = 1;
    
    /* code modified by LLM (iteration 2): updated loop condition and invariants to use int consistently */
    while idx < char_arr@.len()
        invariant
            1 <= idx <= char_arr@.len(),
            forall|i: int| 1 <= i < idx ==> char_arr[0] == #[trigger] char_arr[i],
        decreases char_arr@.len() - idx
    {
        if char_arr[idx] != first_char {
            /* code modified by LLM (iteration 2): assertion now uses int type for indexing */
            assert(char_arr[0] != char_arr[idx]);
            assert(!(forall|i: int| 1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]));
            return false;
        }
        /* code modified by LLM (iteration 2): assertion now uses int type for indexing */
        assert(char_arr[idx] == char_arr[0]);
        idx = idx + 1;
    }
    
    /* code modified by LLM (iteration 2): postcondition assertion remains unchanged */
    assert(forall|i: int| 1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]);
    true
}

} // verus!

fn main() {}