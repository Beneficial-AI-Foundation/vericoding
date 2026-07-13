// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn maximum(xs: Seq<i32>) -> i32 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else if xs.len() == 1 {
        xs[0]
    } else {
        let max_rest = maximum(xs.subrange(1, xs.len() as int));
        if xs[0] > max_rest { xs[0] } else { max_rest }
    }
}

spec fn minimum(xs: Seq<i32>) -> i32 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else if xs.len() == 1 {
        xs[0]
    } else {
        let min_rest = minimum(xs.subrange(1, xs.len() as int));
        if xs[0] < min_rest { xs[0] } else { min_rest }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn smallest_range_ii(nums: Vec<i32>, k: i32) -> (result: i32)
    requires k >= 0
    ensures 
        result >= 0,
        nums.len() == 1 ==> result == 0,
        nums.len() == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {
    // #eval smallest_range_ii([1], 0) == 0
    // #eval smallest_range_ii([0, 10], 2) == 6
    // #eval smallest_range_ii([1, 3, 6], 3) == 3
}