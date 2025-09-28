// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(l1: int, r1: int, l2: int, r2: int, k: int) -> bool {
    l1 <= r1 && l2 <= r2
}

spec fn intersection_left(l1: int, l2: int) -> int {
    if l1 > l2 { l1 } else { l2 }
}

spec fn intersection_right(r1: int, r2: int) -> int {
    if r1 < r2 { r1 } else { r2 }
}

spec fn intersection_size(l1: int, r1: int, l2: int, r2: int) -> int {
    let left = intersection_left(l1, l2);
    let right = intersection_right(r1, r2);
    if right - left + 1 > 0 { right - left + 1 } else { 0 }
}

spec fn k_in_intersection(l1: int, r1: int, l2: int, r2: int, k: int) -> bool {
    let left = intersection_left(l1, l2);
    let right = intersection_right(r1, r2);
    left <= k <= right
}

spec fn expected_result(l1: int, r1: int, l2: int, r2: int, k: int) -> int {
    let intersection_size_val = intersection_size(l1, r1, l2, r2);
    if k_in_intersection(l1, r1, l2, r2, k) {
        if intersection_size_val - 1 > 0 { intersection_size_val - 1 } else { 0 }
    } else {
        intersection_size_val
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Convert proof fns to spec fns for pure computation */
spec fn min(a: i8, b: i8) -> i8 {
    if a <= b { a } else { b }
}

spec fn max(a: i8, b: i8) -> i8 {
    if a >= b { a } else { b }
}

proof fn lemma_intersection_left_right(l1: i8, r1: i8, l2: i8, r2: i8)
    requires
        l1 <= r1,
        l2 <= r2,
    ensures
        max(l1, l2) <= min(r1, r2) || (min(r1, r2) as i16 - max(l1, l2) as i16 + 1 <= 0),
{
}

proof fn lemma_intersection_size_nonnegative(l1: i8, r1: i8, l2: i8, r2: i8)
    requires
        l1 <= r1,
        l2 <= r2,
    ensures
        (if min(r1, r2) >= max(l1, l2) { (min(r1, r2) as i16 - max(l1, l2) as i16 + 1) as i8 } else { 0 }) >= 0,
{
}

proof fn lemma_k_in_intersection_correct(l1: i8, r1: i8, l2: i8, r2: i8, k: i8)
    requires
        l1 <= r1,
        l2 <= r2,
    ensures
        (max(l1, l2) <= k && k <= min(r1, r2)) == (k >= max(l1, l2) && k <= min(r1, r2)),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(l1: i8, r1: i8, l2: i8, r2: i8, k: i8) -> (result: i8)
    requires 
        valid_input(l1 as int, r1 as int, l2 as int, r2 as int, k as int)
    ensures 
        result as int == expected_result(l1 as int, r1 as int, l2 as int, r2 as int, k as int),
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use integer arithmetic without casting to avoid proof mode calls */
    let left_intersection = if l1 > l2 { l1 } else { l2 };
    let right_intersection = if r1 < r2 { r1 } else { r2 };
    
    let intersection_size_val = if right_intersection >= left_intersection {
        (right_intersection as i16 - left_intersection as i16 + 1) as i8
    } else {
        0i8
    };
    
    let result = if k >= left_intersection && k <= right_intersection {
        if intersection_size_val > 1 {
            intersection_size_val - 1
        } else {
            0
        }
    } else {
        intersection_size_val
    };
    
    result
}
// </vc-code>


}

fn main() {}