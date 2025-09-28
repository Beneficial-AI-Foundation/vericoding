// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn search_insert(xs: &Vec<i32>, target: i32) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
    ensures
        result <= xs.len(),
        forall|i: int| 0 <= i < result ==> xs[i] < target,
        result < xs.len() ==> target <= xs[result as int],
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = xs.len();
    while low < high
        invariant
            0 <= low <= high <= xs.len(),
            forall|i: int| 0 <= i < low ==> xs[i] < target,
            forall|i: int| (high as int) <= i < xs.len() ==> target <= xs[i],
            forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j],
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        if xs[mid] < target {
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