use vstd::prelude::*;

fn main() {
}

verus! {

fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
{
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l < i + 1 && l == k + 1 ==> (arr[k] + 1 == arr[l]),
    {
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i += 1;
    }
    return true;
}

} // verus!