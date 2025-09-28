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
/* code modified by LLM (iteration 5): added braces for invariant forall to fix compilation */
    let mut i: int = 0;
    while i < arr@.len()
        invariant 0 <= i <= arr@.len()
        invariant forall |k: int| { 0 <= k < i ==> (arr@[k] as int) % 2 == 0 }
        decreases arr@.len() - i
    {
        if (arr@[i] as int) % 2 != 0 {
            proof {
                assert(forall |k: int| 0 <= k < i ==> (arr@[k] as int) % 2 == 0);
                assert(arr@.take(i) == arr@.take(i).filter(|x: u32| (x as int) % 2 == 0)) by {
                    assert forall |j: int| 0 <= j < i ==> (|x: u32| (x as int) % 2 == 0)(arr@[j]);
                }
                assert((arr@[i] as int) % 2 != 0);
            }
            return Some(i as usize);
        }
        i = i + 1;
    }
    proof {
        assert(forall |k: int| 0 <= k < arr@.len() ==> (arr@[k] as int) % 2 == 0);
    }
    None
}
// </vc-code>

}
fn main() {}