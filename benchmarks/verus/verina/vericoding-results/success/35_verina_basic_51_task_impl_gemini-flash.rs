// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_search_precond(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers provided in previous iteration. */
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &Vec<i32>, key: i32) -> (result: usize)
    requires binary_search_precond(a, key),
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added decreases clause to the `while` loop. */
{
    let mut low: usize = 0;
    let mut high: usize = a.len();

    while low < high
        invariant
            0 <= low,
            low <= high,
            high <= a.len(),
            forall|i: int| 0 <= i < low ==> a[i] < key,
            forall|i: int| high <= i < a.len() ==> a[i] >= key,
            binary_search_precond(a, key),
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        if a[mid] < key {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

}
fn main() {}