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
/* helper modified by LLM (iteration 5): Added `/*` and `*/` wrapper for the comment */
spec fn is_even(n: u32) -> bool { n % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error: `i = i = i + 1;` -> `i = i + 1;` */
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            forall|k: int| 0 <= k < i ==> is_even(arr[k as int]),
        decreases arr.len() - i
    {
        if arr[i] % 2 != 0 {
            // If arr[i] is odd, then all elements before it must be even.
            // The invariant already ensures this for k < i.
            // We are returning Some(i), so the `check_find_first_odd` postcondition requires
            // arr[idx as int] % 2 != 0 (which is arr[i]) AND
            // arr@.take(idx as int) == arr@.take(idx as int).filter(|x: u32| x % 2 == 0)
            // The forall in the invariant takes care of the second part.
            return Some(i);
        }
        // If arr[i] is even, we continue the loop.
        // The `forall` invariant needs to hold for `i+1` in the next iteration.
        proof {
            assert(is_even(arr[i as int]));
        }
        i = i + 1;
    }
    // If the loop finishes, no odd number was found.
    // The `check_find_first_odd` postcondition requires forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    // The invariant at the end of the loop (where i == arr.len()) is:
    // forall|k: int| 0 <= k < arr.len() ==> is_even(arr[k as int]), which is exactly what is needed.
    None
}
// </vc-code>

}
fn main() {}