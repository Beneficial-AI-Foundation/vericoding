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
/* helper modified by LLM (iteration 3): No changes needed as helpers are implemented in preamble */
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
/* code modified by LLM (iteration 3): Fixed compilation error by using i32 for intermediate computations and 'as int' only in proof blocks */
{
    let l1_i = l1 as i32;
    let r1_i = r1 as i32;
    let l2_i = l2 as i32;
    let r2_i = r2 as i32;
    let k_i = k as i32;
    let left = if l1_i > l2_i { l1_i } else { l2_i };
    let right = if r1_i < r2_i { r1_i } else { r2_i };
    let size = if left <= right { right - left + 1 } else { 0 };
    let in_int = left <= k_i && k_i <= right;
    let result_i = if in_int { if size > 0 { size - 1 } else { 0 } } else { size };
    proof {
        let l1_spec = l1 as int;
        let r1_spec = r1 as int;
        let l2_spec = l2 as int;
        let r2_spec = r2 as int;
        let k_spec = k as int;
        assert(left as int == intersection_left(l1_spec, l2_spec));
        assert(right as int == intersection_right(r1_spec, r2_spec));
        assert(size as int == intersection_size(l1_spec, r1_spec, l2_spec, r2_spec));
        assert(in_int as int == k_in_intersection(l1_spec, r1_spec, l2_spec, r2_spec, k_spec) as int);
        assert(result_i as int == expected_result(l1_spec, r1_spec, l2_spec, r2_spec, k_spec));
    }
    result_i as i8
}
// </vc-code>


}

fn main() {}