// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helper section needed. */
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the postcondition issue. The loop invariant now correctly tracks that the key has not been found in the elements checked so far. */
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j as usize] != key,
        decreases (a.len() - i)
    {
        if a[i] == key {
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}