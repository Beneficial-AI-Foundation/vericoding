// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */


// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added `a.len()` to invariant for better bounds checking, and `i as int` type safety for postconditions */
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != key,
        decreases a.len() - i
    {
        if a[i] == key {
            // The following ensures for `i as i32` that `0 <= i as int` and `i as int < a.len()` and also `a[i as int] == key`.
            // The loop invariant ensures `forall|j: int| 0 <= j < i ==> a[j] != key`.
            return i as i32;
        }
        i = i + 1;
    }
    // If the loop finishes, it means `forall|j: int| 0 <= j < a.len() ==> a[j] != key`
    -1
}
// </vc-code>

}
fn main() {}