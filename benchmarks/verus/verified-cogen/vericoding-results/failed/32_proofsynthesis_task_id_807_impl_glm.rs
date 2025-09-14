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
/* code modified by LLM (iteration 5): fixed loop invariant syntax by removing commas */ {
    let mut i: int = 0;
    let n = arr@.len();
    while i < n 
        invariant 0 <= i <= n
        invariant forall|j: int| 0 <= j < i ==> arr[j as usize] % 2 == 0
        decreases n - i
    {
        if arr[i as usize] % 2 != 0 {
            return Some(i as usize);
        }
        i = i + 1;
    }
    return None;
}
// </vc-code>

}
fn main() {}