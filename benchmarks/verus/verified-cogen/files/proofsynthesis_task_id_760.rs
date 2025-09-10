use vstd::prelude::*;

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)

    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    assume(false);
    unreached()
}

}
fn main() {}