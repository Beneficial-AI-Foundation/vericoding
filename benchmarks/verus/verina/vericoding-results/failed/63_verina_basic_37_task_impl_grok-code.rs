// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        (result >= 0 ==> {
            &&& 0 <= result < arr.len()
            &&& arr[result as int] == target
            &&& forall|i: int| 0 <= i < result ==> arr[i] != target
        }) &&
        (result == -1 ==> {
            &&& forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
        }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation error by correcting typo in return statement */
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            forall|t: usize| t < i ==> arr@[t as int] != target,
        decreases arr.len() - i
    {
        if arr[i] == target {
            #[verifier::truncate] return i as i32;
        }
        i += 1;
    }
    return -1;
}
// </vc-code>

}
fn main() {}