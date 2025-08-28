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

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    // post-conditions-start
    ensures check_find_first_odd(arr, index),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-code>

} // verus!

fn main() {}