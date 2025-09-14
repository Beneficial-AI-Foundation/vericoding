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
/* helper modified by LLM (iteration 5): Added decreases clause to recursive proof function */
proof fn all_even_up_to(arr: &Vec<u32>, idx: int) 
    requires 0 <= idx <= arr.len()
    ensures arr@.take(idx).filter(|x| is_odd(x)) == Seq::<u32>::empty()
    decreases idx
{
    if idx == 0 {
        assert(arr@.take(0) == Seq::<u32>::empty());
    } else {
        all_even_up_to(arr, idx - 1);
        assert(arr@.take(idx) == arr@.take(idx - 1).push(arr@[idx - 1]));
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)

    ensures check_find_first_odd(arr, index),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Maintained implementation with proper proof function calls */
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
    {
        if arr[i] % 2 != 0 {
            proof {
                all_even_up_to(arr, i as int);
            }
            return Some(i);
        }
        i += 1;
    }
    proof {
        all_even_up_to(arr, arr.len() as int);
    }
    None
}
// </vc-code>

}
fn main() {}