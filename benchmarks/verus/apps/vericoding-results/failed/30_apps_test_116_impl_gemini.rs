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
/* helper modified by LLM (iteration 2): [Updated ensures clause to directly reference spec function] */
fn max_i8(a: i8, b: i8) -> (res: i8)
    ensures res as int == intersection_left(a as int, b as int)
{
    if a > b { a } else { b }
}

/* helper modified by LLM (iteration 2): [Updated ensures clause to directly reference spec function] */
fn min_i8(a: i8, b: i8) -> (res: i8)
    ensures res as int == intersection_right(a as int, b as int)
{
    if a < b { a } else { b }
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
    /* code modified by LLM (iteration 2): [Used executable integer types for calculations.] */
    let left = max_i8(l1, l2);
    let right = min_i8(r1, r2);

    let intersection_size_val: i16;
    if left > right {
        intersection_size_val = 0;
    } else {
        intersection_size_val = (right as i16) - (left as i16) + 1;
    }

    let k_in_intersection = left <= k && k <= right;

    let result_val: i16 = if k_in_intersection {
        let one_less = intersection_size_val - 1;
        if one_less > 0 {
            one_less
        } else {
            0
        }
    } else {
        intersection_size_val
    };

    result_val as i8
}
// </vc-code>


}

fn main() {}