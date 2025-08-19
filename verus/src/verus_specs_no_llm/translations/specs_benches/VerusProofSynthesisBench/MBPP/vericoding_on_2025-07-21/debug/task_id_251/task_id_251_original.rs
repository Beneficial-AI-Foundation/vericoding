use vstd::prelude::*;

verus! {

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
