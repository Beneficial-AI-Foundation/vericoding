use vstd::prelude::*;


verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn all_characters_same(char_arr: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if char_arr.len() == 0 {
        return true;
    }
    
    let first_char = char_arr[0];
    
    /* code modified by LLM (iteration 5): fixed type mismatch by casting i to int for indexing */
    for i in 1..char_arr.len()
        invariant
            forall|j: int| 1 <= j < i ==> char_arr[0] == #[trigger] char_arr[j as int]
    {
        if char_arr[i] != first_char {
            /* code modified by LLM (iteration 5): added proof block to show postcondition is false with proper triggers */
            proof {
                assert(char_arr[0] != char_arr[i as int]);
                assert(1 <= i < char_arr@.len());
                assert(!(forall|k: int| 1 <= k < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[k as int]));
            }
            return false;
        }
        /* code modified by LLM (iteration 5): added proof to maintain invariant */
        proof {
            assert(char_arr[i as int] == first_char);
            assert(char_arr[0] == first_char);
            assert(char_arr[0] == char_arr[i as int]);
        }
    }
    
    /* code modified by LLM (iteration 5): added proof to establish postcondition when returning true */
    proof {
        assert(forall|j: int| 1 <= j < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[j as int]);
    }
    true
}
// </vc-code>

} // verus!

fn main() {}