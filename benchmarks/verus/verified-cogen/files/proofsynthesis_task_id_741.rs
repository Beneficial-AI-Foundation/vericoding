use vstd::prelude::*;

verus! {

fn all_characters_same(char_arr: &Vec<char>) -> (result: bool)

    ensures
        result == (forall|i: int|
            1 <= i < char_arr@.len() ==> char_arr[0] == #[trigger] char_arr[i]),
{
    assume(false);
    unreached();
}

}
fn main() {}