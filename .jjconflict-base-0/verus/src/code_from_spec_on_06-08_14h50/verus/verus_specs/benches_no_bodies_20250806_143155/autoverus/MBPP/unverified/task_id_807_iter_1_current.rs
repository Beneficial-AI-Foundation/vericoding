use vstd::prelude::*;

fn main() {}

verus! {

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures
        if let Some(idx) = index {
            idx < arr.len() && arr[idx] % 2 == 1 && forall|k: int| 0 <= k < idx ==> (arr[k] % 2 == 0)
        } else {
            forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
        },
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> (arr[k] % 2 == 0),
    {
        if arr[index] % 2 != 0 {
            return Some(index);
        }
        index += 1;
    }
    None
}

} // verus!