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
/* helper modified by LLM (iteration 5): Fixed parameter list in helper function */
proof fn intersection_size_bounds(l1: i8, r1: i8, l2: i8, r2: i8)
    requires valid_input(l1 as int, r1 as int, l2 as int, r2 as int, 0),
    ensures 
        intersection_size(l1 as int, r1 as int, l2 as int, r2 as int) >= 0,
        intersection_size(l1 as int, r1 as int, l2 as int, r2 as int) <= i8::MAX as int,
{
    let left = intersection_left(l1 as int, l2 as int);
    let right = intersection_right(r1 as int, r2 as int);
    
    if right - left + 1 > 0 {
        assert(left >= l1 as int || left >= l2 as int);
        assert(right <= r1 as int || right <= r2 as int);
        assert(left <= right);
        assert(right - left + 1 <= r1 - l1 + 1 || right - left + 1 <= r2 - l2 + 1);
        assert(right - left + 1 <= i8::MAX as int);
    }
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
    /* code modified by LLM (iteration 5): Compute intersection size accounting for k */
    let left = if l1 > l2 { l1 } else { l2 };
    let right = if r1 < r2 { r1 } else { r2 };
    
    if right >= left {
        assert(left as int == intersection_left(l1 as int, l2 as int));
        assert(right as int == intersection_right(r1 as int, r2 as int));
        assert(0 <= right - left);
        assert(right - left <= i8::MAX - 1);
        
        let size: i8 = (right - left) as i8 + 1;
        assert(size as int == right as int - left as int + 1);
        assert(size >= 0);
        assert(size as int == intersection_size(l1 as int, r1 as int, l2 as int, r2 as int));
        
        if left <= k && k <= right {
            assert(k_in_intersection(l1 as int, r1 as int, l2 as int, r2 as int, k as int));
            if size > 1 {
                let result = size - 1;
                assert(result as int == intersection_size(l1 as int, r1 as int, l2 as int, r2 as int) - 1);
                result
            } else {
                assert(intersection_size(l1 as int, r1 as int, l2 as int, r2 as int) == 1);
                0
            }
        } else {
            assert(!k_in_intersection(l1 as int, r1 as int, l2 as int, r2 as int, k as int));
            assert(size as int == intersection_size(l1 as int, r1 as int, l2 as int, r2 as int));
            size
        }
    } else {
        assert(intersection_size(l1 as int, r1 as int, l2 as int, r2 as int) == 0);
        0
    }
}
// </vc-code>


}

fn main() {}