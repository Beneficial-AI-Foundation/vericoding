use vstd::prelude::*;

verus! {

fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
{
    assume(false);
    unreached()
}

}
fn main() {}