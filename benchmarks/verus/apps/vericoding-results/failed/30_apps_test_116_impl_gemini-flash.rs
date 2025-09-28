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
/* helper modified by LLM (iteration 5): The previous iteration did not have any functional changes from the previous one, so this helper section is kept empty. */
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
/* code modified by LLM (iteration 5): Add explicit `as int` casts to handle potential overflow while computing `current_size` and verifying `expected_result` */
{
    let inter_left = if l1 > l2 { l1 } else { l2 };
    let inter_right = if r1 < r2 { r1 } else { r2 };

    let mut final_result: i8 = 0;

    if inter_left <= inter_right {
        // There is an overlap
        let current_size = (inter_right as int - inter_left as int + 1) as i8;

        if inter_left <= k && k <= inter_right {
            final_result = current_size - 1;
        } else {
            final_result = current_size;
        }
    } else {
        // No overlap
        final_result = 0;
    }

    proof {
        let ghost left1 = l1 as int;
        let ghost right1 = r1 as int;
        let ghost left2 = l2 as int;
        let ghost right2 = r2 as int;
        let ghost k_int = k as int;

        let ghost inter_left_spec = intersection_left(left1, left2);
        let ghost inter_right_spec = intersection_right(right1, right2);

        assert(inter_left_spec == inter_left as int);
        assert(inter_right_spec == inter_right as int);
        
        let ghost intersection_size_val_spec = intersection_size(left1, right1, left2, right2);
        let ghost k_in_intersection_val_spec = k_in_intersection(left1, right1, left2, right2, k_int);

        if inter_left <= inter_right {
            let ghost current_size_int = (inter_right as int) - (inter_left as int) + 1;

            if inter_left <= k && k <= inter_right {
                assert(k_in_intersection_val_spec);
                assert(expected_result(left1, right1, left2, right2, k_int) == current_size_int - 1);
                assert(final_result as int == current_size_int - 1);
            } else {
                assert(!k_in_intersection_val_spec);
                assert(expected_result(left1, right1, left2, right2, k_int) == current_size_int);
                assert(final_result as int == current_size_int);
            }
        } else {
           assert(intersection_size_val_spec == 0);
           assert(expected_result(left1, right1, left2, right2, k_int) == 0);
           assert(final_result == 0);
        }
    }

    final_result
}
// </vc-code>


}

fn main() {}