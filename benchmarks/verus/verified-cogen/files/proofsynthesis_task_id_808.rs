use vstd::prelude::*;

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    assume(false);
    unreached()
}

}
fn main() {}