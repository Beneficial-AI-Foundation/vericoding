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
/* helper modified by LLM (iteration 5): fixed syntax error by removing incorrect type conversion */
fn intersection_boundaries(l1: i8, r1: i8, l2: i8, r2: i8) -> (i8, i8)
    ensures
        let (left, right) = result;
        left == intersection_left(l1 as int, l2 as int) as i8,
        right == intersection_right(r1 as int, r2 as int) as i8
{
    let left = if l1 > l2 { l1 } else { l2 };
    let right = if r1 < r2 { r1 } else { r2 };
    (left, right)
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
/* code modified by LLM (iteration 5): removed incorrect type conversion in ensures clause */
{
    let (left, right) = intersection_boundaries(l1, r1, l2, r2);
    
    // Convert to int for precise arithmetic without overflow
    let left_int = left as int;
    let right_int = right as int;
    let k_int = k as int;
    
    // Compute intersection size using int arithmetic
    let size_int = if right_int < left_int {
        0
    } else {
        right_int - left_int + 1
    };
    
    // Check if k is in intersection
    let in_intersection = left_int <= k_int && k_int <= right_int;
    
    // Compute result using int arithmetic
    let result_int = if in_intersection {
        if size_int - 1 > 0 { size_int - 1 } else { 0 }
    } else {
        size_int
    };
    
    // Safe cast to i8 - we rely on the verifier to check the bounds
    result_int as i8
}
// </vc-code>


}

fn main() {}