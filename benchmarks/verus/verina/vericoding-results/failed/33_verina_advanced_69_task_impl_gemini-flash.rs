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
/* code modified by LLM (iteration 5): Fixed compilation error by changing 'len' to 'usize' and using `high` as 'usize' for array indexing, then converting to 'int' only for ghost code. */
{
    let len: usize = xs.len();

    let mut low: usize = 0;
    let mut high: usize = len;

    while low < high
        invariant
            0 <= low,
            low <= high,
            high <= len,
            forall|i: int| 0 <= i < low ==> xs@[i] < target,
            forall|i: int| high <= i < len ==> xs@[i] >= target,
    {
        let mid = low + (high - low) / 2;

        if xs@[mid] < target {
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