// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn maximum(xs: Seq<i32>) -> i32 {
    if xs.len() == 0 {
        0
    } else {
        if xs.len() == 1 {
            if xs[0] > 0 { xs[0] } else { 0 }
        } else {
            let max_rest = maximum(xs.skip(1));
            if xs[0] > max_rest { xs[0] } else { max_rest }
        }
    }
}

spec fn sum(xs: Seq<i32>) -> i32 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        xs[0] + sum(xs.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
spec fn max_sum_spec(arr: Seq<i32>) -> i32 {
    if arr.len() == 0 {
        0
    } else {
        maximum(arr)
    }
}

fn max_sum(arr: Vec<i32>) -> (result: i32)
    requires arr.len() > 0,
    ensures result == max_sum_spec(arr@)

fn solve(arr: Vec<i32>, k: usize) -> (result: i32)
    requires arr.len() > 0,
    requires k > 0,
    ensures result >= max_sum_spec(arr@)
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
    // Apps difficulty: interview
    // Assurance level: guarded_and_plausible

    // #guard_msgs in
    // #eval solve [1, 2] 3

    // #guard_msgs in
    // #eval solve [1, -2, 1] 2

    // #guard_msgs in
    // #eval solve [-1, -2, -3] 4
}