// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_characters_same(char_arr: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added trigger to loop invariant */
    if char_arr.len() <= 1 {
        return true;
    }

    let mut i: usize = 1;
    while i < char_arr.len()
        invariant
            char_arr@.len() > 1,
            1 <= i <= char_arr@.len(),
            forall|j: int| 1 <= j < i ==> char_arr@[0] == #[trigger] char_arr@[j],
        decreases char_arr.len() - i
    {
        if char_arr[i] != char_arr[0] {
            return false;
        }
        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}