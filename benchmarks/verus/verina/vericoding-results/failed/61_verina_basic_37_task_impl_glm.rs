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
{
    /* code modified by LLM (iteration 5): fixed invariant syntax by removing extra curly braces */
    let mut i: int = 0;
    while i < (arr.len() as int)
        invariant 0 <= i <= arr.len() as int
        invariant forall|j: int| 0 <= j < i ==> arr[j] != target
    {
        if arr[i as usize] == target {
            return i as i32;
        }
        i += 1;
    }
    -1
}
// </vc-code>

}
fn main() {}