// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed filter equality proof */
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            proof {
                let take_i = arr@.take(i as int);
                let filtered = take_i.filter(|x: u32| x % 2 == 0);
                assert(take_i.len() == i);
                assert(forall|j: int| 0 <= j < i ==> take_i[j] == arr[j]);
                assert(forall|j: int| 0 <= j < i ==> take_i[j] % 2 == 0);
                assert(forall|j: int| 0 <= j < take_i.len() ==> take_i[j] % 2 == 0);
                assert(take_i =~= filtered);
            }
            return Some(i);
        }
        i = i + 1;
    }
    None
}
// </vc-code>

}
fn main() {}