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
    /* code modified by LLM (iteration 5): Fixed trigger annotation for quantifier */
    let mut left: usize = 0;
    let mut right: usize = xs.len();
    
    while left < right
        invariant
            left <= right,
            right <= xs.len(),
            forall|i: int| 0 <= i < left ==> xs[i] < target,
            right < xs.len() ==> target <= xs[right as int],
        decreases right - left,
    {
        let mid = left + (right - left) / 2;
        
        if xs[mid] < target {
            proof {
                assert(xs[mid as int] < target);
                assert(forall|i: int| 0 <= i < left ==> xs[i] < target);
                // Use the sorted property from precondition
                assert(forall|i: int, j: int| 0 <= i < j < xs.len() ==> xs[i] < xs[j]);
                // All elements before mid are less than xs[mid]
                assert(forall|i: int| #[trigger] xs[i] && 0 <= i < mid ==> xs[i] < xs[mid as int]);
                // Since xs[mid] < target and all xs[i] < xs[mid] for i < mid
                assert(forall|i: int| 0 <= i < mid ==> xs[i] < target);
                // Combined with existing invariant
                assert(forall|i: int| 0 <= i <= mid ==> xs[i] < target);
            }
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