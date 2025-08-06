use vstd::prelude::*;

fn main() {}

verus! {

fn all_characters_same(char_arr: &[u8]) -> (result: bool)
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
{
    if char_arr.len() == 0 {
        return true;
    }
    
    let first_char = char_arr[0];
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < char_arr.len()
        invariant
            1 <= idx <= char_arr@.len(),
            forall|j: int| 1 <= j < idx ==> char_arr[0] == char_arr[j],
        decreases char_arr@.len() - idx
    {
        if char_arr[idx] != first_char {
            return false;
        }
        idx += 1;
    }
    
    true
}

} // verus!