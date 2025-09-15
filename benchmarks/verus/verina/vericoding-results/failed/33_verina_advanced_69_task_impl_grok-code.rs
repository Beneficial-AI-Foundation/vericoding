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
/* code modified by LLM (iteration 5): Fixed indentation of while loop specifications and used @ indexing with int for vector access to resolve compilation error. */
{
    let mut left: usize = 0;
    let mut right: usize = xs.len();
    while (left < right)
        decreases right - left
        invariant
            0 <= left as int <= right as int <= xs.len() as int,
            forall |i: int| 0 <= i < left as int ==> xs@[i] < target,
            forall |i: int| right as int <= i < xs.len() as int ==> target <= xs@[i],
    {
        let mid = left + ((right - left) / 2);
        if xs@[mid as int] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    left
}
// </vc-code>

}
fn main() {}