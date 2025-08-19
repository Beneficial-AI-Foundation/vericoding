use vstd::prelude::*;

verus! {

fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|m: int| 0 <= m < index ==> (arr[m] != k),
    {
        if (arr[index] == k) {
            return true;
        }
        index += 1;
    }
    false
}

fn main() {}

} // verus!
