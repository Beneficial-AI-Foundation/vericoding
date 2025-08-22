use vstd::prelude::*;

fn main() {
}

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
    
    for i in 1..char_arr.len()
        invariant
            /* code modified by LLM (iteration 1): added trigger annotation to fix quantifier inference error */
            forall|j: int| 1 <= j < i ==> char_arr[0] == #[trigger] char_arr[j],
    {
        if char_arr[i] != first_char {
            return false;
        }
    }
    
    true
}

} // verus!