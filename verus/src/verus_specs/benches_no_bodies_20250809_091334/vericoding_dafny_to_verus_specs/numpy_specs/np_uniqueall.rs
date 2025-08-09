use vstd::prelude::*;

verus! {

fn unique_all(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> exists|j: int| 0 <= j < ret.len() && #[trigger] ret[j] == #[trigger] arr[i],
        forall|i: int, j: int| 0 <= i < ret.len() && 0 <= j < i ==> ret[i] != ret[j],
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}

fn main() {}