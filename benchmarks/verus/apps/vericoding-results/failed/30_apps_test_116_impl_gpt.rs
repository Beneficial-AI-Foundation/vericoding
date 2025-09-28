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
/* helper modified by LLM (iteration 2): prove intersection_size non-negative */
proof fn lemma_intersection_size_nonneg(l1: int, r1: int, l2: int, r2: int)
    ensures
        intersection_size(l1, r1, l2, r2) >= 0,
{
    let left = intersection_left(l1, l2);
    let right = intersection_right(r1, r2);
    if right - left + 1 > 0 {
        assert(intersection_size(l1, r1, l2, r2) == right - left + 1);
        assert(intersection_size(l1, r1, l2, r2) >= 0);
    } else {
        assert(intersection_size(l1, r1, l2, r2) == 0);
        assert(intersection_size(l1, r1, l2, r2) >= 0);
    }
}

/* helper modified by LLM (iteration 2): prove expected_result non-negative */
proof fn lemma_expected_result_nonneg(l1: int, r1: int, l2: int, r2: int, k: int)
    ensures
        expected_result(l1, r1, l2, r2, k) >= 0,
{
    lemma_intersection_size_nonneg(l1, r1, l2, r2);
    let sz = intersection_size(l1, r1, l2, r2);
    if k_in_intersection(l1, r1, l2, r2, k) {
        if sz - 1 > 0 {
            assert(expected_result(l1, r1, l2, r2, k) == sz - 1);
            assert(expected_result(l1, r1, l2, r2, k) >= 0);
        } else {
            assert(expected_result(l1, r1, l2, r2, k) == 0);
            assert(expected_result(l1, r1, l2, r2, k) >= 0);
        }
    } else {
        assert(expected_result(l1, r1, l2, r2, k) == sz);
        assert(expected_result(l1, r1, l2, r2, k) >= 0);
    }
}

/* helper modified by LLM (iteration 2): unfold expected_result cases */
proof fn lemma_expected_result_unfold(l1: int, r1: int, l2: int, r2: int, k: int)
    ensures
        expected_result(l1, r1, l2, r2, k) ==
            if k_in_intersection(l1, r1, l2, r2, k) {
                let sz = intersection_size(l1, r1, l2, r2);
                if sz - 1 > 0 { sz - 1 } else { 0 }
            } else {
                intersection_size(l1, r1, l2, r2)
            },
{
    let sz = intersection_size(l1, r1, l2, r2);
    if k_in_intersection(l1, r1, l2, r2, k) {
        if sz - 1 > 0 {
            assert(expected_result(l1, r1, l2, r2, k) == sz - 1);
        } else {
            assert(expected_result(l1, r1, l2, r2, k) == 0);
        }
    } else {
        assert(expected_result(l1, r1, l2, r2, k) == sz);
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
    /* code modified by LLM (iteration 2): use only machine integers in exec code (i16) to avoid 'int' in exec; compute intersection and clamp to [0,127] */
    let li: i16 = l1 as i16;
    let ri: i16 = r1 as i16;
    let lj: i16 = l2 as i16;
    let rj: i16 = r2 as i16;

    let left: i16 = if li > lj { li } else { lj };
    let right: i16 = if ri < rj { ri } else { rj };

    let size: i16 = if right >= left { (right - left) + 1 } else { 0 };
    let in_it: bool = (k as i16) >= left && (k as i16) <= right;

    let ans: i16 = if in_it {
        if size > 1 { size - 1 } else { 0 }
    } else {
        size
    };

    proof {
        // Ghost reasoning only
        lemma_intersection_size_nonneg(l1 as int, r1 as int, l2 as int, r2 as int);
        lemma_expected_result_nonneg(l1 as int, r1 as int, l2 as int, r2 as int, k as int);
    }

    let clamped: i16 = if ans < 0 { 0 } else if ans > 127 { 127 } else { ans };
    let result: i8 = clamped as i8;
    result
}
// </vc-code>


}

fn main() {}