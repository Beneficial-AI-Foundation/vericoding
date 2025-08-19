use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
        &&& arr[idx as int] % 2 != 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}
// pure-end

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    // post-conditions-start
    ensures check_find_first_odd(arr, index),
    // post-conditions-end
{
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
    {
        if arr[i] % 2 != 0 {
            assert(arr@.take(i as int) == arr@.take(i as int).filter(|x: u32| x % 2 == 0)) by {
                assert forall|k: int| 0 <= k < i implies arr[k] % 2 == 0 by {};
            };
            return Some(i);
        }
    }
    None
}

} // verus!

fn main() {}