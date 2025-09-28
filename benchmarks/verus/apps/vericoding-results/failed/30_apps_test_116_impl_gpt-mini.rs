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
/* helper modified by LLM (iteration 5): spec int_max */
spec fn int_max(a: int, b: int) -> int { if a > b { a } else { b } }

/* helper modified by LLM (iteration 5): spec int_min */
spec fn int_min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 5): use ghost ints for arithmetic and proofs; compute result as i8 cast from ghost */
    let ghost l1_int: int = l1 as int;
    let ghost r1_int: int = r1 as int;
    let ghost l2_int: int = l2 as int;
    let ghost r2_int: int = r2 as int;
    let ghost k_int: int = k as int;

    let ghost left_int: int = if l1_int > l2_int { l1_int } else { l2_int };
    let ghost right_int: int = if r1_int < r2_int { r1_int } else { r2_int };
    let ghost raw: int = right_int - left_int + 1;
    let ghost inter_int: int = if raw > 0 { raw } else { 0 };

    let ghost result_int: int = if left_int <= k_int && k_int <= right_int {
        let ghost dec: int = inter_int - 1;
        if dec > 0 { dec } else { 0 }
    } else {
        inter_int
    };

    proof {
        assert(left_int == intersection_left(l1 as int, l2 as int));
        assert(right_int == intersection_right(r1 as int, r2 as int));
        assert(inter_int == intersection_size(l1 as int, r1 as int, l2 as int, r2 as int));
        if left_int <= k_int && k_int <= right_int {
            assert(k_in_intersection(l1 as int, r1 as int, l2 as int, r2 as int, k as int));
            assert(result_int == (if inter_int - 1 > 0 { inter_int - 1 } else { 0 }));
            assert(expected_result(l1 as int, r1 as int, l2 as int, r2 as int, k as int) == result_int);
        } else {
            assert(!(left_int <= k_int && k_int <= right_int));
            assert(!(k_in_intersection(l1 as int, r1 as int, l2 as int, r2 as int, k as int)));
            assert(expected_result(l1 as int, r1 as int, l2 as int, r2 as int, k as int) == result_int);
        }
        assert(result_int == expected_result(l1 as int, r1 as int, l2 as int, r2 as int, k as int));
    }

    let result: i8 = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}