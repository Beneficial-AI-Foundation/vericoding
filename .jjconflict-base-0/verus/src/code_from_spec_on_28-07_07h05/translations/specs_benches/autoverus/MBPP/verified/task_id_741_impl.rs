use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn all_characters_same(char_arr: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
{
    if char_arr.len() <= 1 {
        return true;
    }
    
    let first_char = char_arr[0];
    for i in 1..char_arr.len()
        invariant
            /* code modified by LLM (iteration 2): Fixed invariant to properly track that all checked characters match */
            forall|j: int| 1 <= j < i ==> char_arr[0] == #[trigger] char_arr[j]
    {
        if char_arr[i] != first_char {
            /* code modified by LLM (iteration 3): Fixed type mismatch by casting i to int */
            assert(char_arr[0] != char_arr[i as int]);
            /* code modified by LLM (iteration 4): Added trigger annotation to fix quantifier trigger inference */
            assert(!(forall|k: int| 1 <= k < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[k]));
            return false;
        }
        /* code modified by LLM (iteration 3): Fixed type mismatch by casting i to int */
        assert(char_arr[0] == char_arr[i as int]);
    }
    /* code modified by LLM (iteration 2): Added assertion to help prove postcondition when returning true */
    assert(forall|j: int| 1 <= j < char_arr@.len() ==> char_arr[0] == char_arr[j]);
    true
}

} // verus!