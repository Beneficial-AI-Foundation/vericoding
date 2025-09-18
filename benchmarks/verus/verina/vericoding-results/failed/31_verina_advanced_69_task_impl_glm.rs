// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_less_than_target_before_index(xs: &Vec<i32>, index: int, target: i32) -> bool {
    forall|i: int| 0 <= i < index ==> xs[i] < target
}

spec fn target_less_than_or_equal_from_index(xs: &Vec<i32>, index: int, target: i32) -> bool {
    index < xs.len() ==> target <= xs[index as int]
}
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
/* code modified by LLM (iteration 5): fixed type errors in proof block */
{
    let mut low = 0;
    let mut high = xs.len();
    
    while low < high
        invariant
            0 <= low as int <= high as int <= xs.len() as int,
            all_less_than_target_before_index(xs, low as int, target),
            target_less_than_or_equal_from_index(xs, high as int, target),
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        if xs[mid] < target {
            proof {
                assert forall|i: int| low as int <= i < (mid as int) + 1 implies xs[i] < target by {
                    if i < mid as int {
                        assert(xs@[i] < xs@[mid as int]);
                    } else {
                        assert(i == mid as int);
                    }
                    assert(xs@[i] < target);
                };
            }
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