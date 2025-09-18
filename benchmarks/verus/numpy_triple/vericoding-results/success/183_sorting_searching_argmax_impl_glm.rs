// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(a: Vec<i32>) -> (result: usize)
    requires a.len() > 0,
    ensures 
        result < a.len(),
        forall|j: int| 0 <= j < a.len() ==> a[j] <= a[result as int],
        forall|j: int| 0 <= j < a.len() && a[j] == a[result as int] ==> result <= j as usize,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type errors in loop invariant */
{
    let mut best_index = 0;
    for i in 1..a.len()
        invariant 
            0 <= best_index < i,
            forall|j: int| 0 <= j < i ==> a[j] <= a[best_index as int],
            forall|j: int| 0 <= j < i && a[j] == a[best_index as int] ==> best_index <= j as usize
    {
        if a[i] > a[best_index] {
            best_index = i;
        } else if a[i] == a[best_index] {
            // do nothing
        }
    }
    best_index
}
// </vc-code>

}
fn main() {}