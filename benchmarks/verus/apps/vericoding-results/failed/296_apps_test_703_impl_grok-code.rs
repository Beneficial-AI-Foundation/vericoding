// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn valid_input(k: int, a: int, b: int, v: int) -> bool {
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

spec fn box_capacity(num_boxes: int, k: int, b: int, v: int) -> int
    recommends num_boxes >= 0
{
    v * (num_boxes + min(b, (k - 1) * num_boxes))
}

spec fn can_store_nuts(num_boxes: int, k: int, a: int, b: int, v: int) -> bool
    recommends num_boxes >= 0
{
    a <= box_capacity(num_boxes, k, b, v)
}

spec fn is_minimal_solution(result: int, k: int, a: int, b: int, v: int) -> bool
    recommends result >= 1
{
    can_store_nuts(result, k, a, b, v) &&
    (result == 1 || !can_store_nuts(result - 1, k, a, b, v))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): defined executable versions of spec functions used in exec code to fix compilation error */
fn min_exec(x: i64, y: i64) -> i64 {
    if x <= y { x } else { y }
}

fn box_capacity_exec(num_boxes: i64, k: i64, b: i64, v: i64) -> i64 {
    v * (num_boxes + min_exec(b, (k - 1) * num_boxes))
}

fn can_store_nuts_exec(num_boxes: i64, k: i64, a: i64, b: i64, v: i64) -> bool {
    a <= box_capacity_exec(num_boxes, k, b, v)
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8, v: i8) -> (result: i8)
    requires
        valid_input(k as int, a as int, b as int, v as int)
    ensures
        result >= 1,
        result <= 127,
        is_minimal_solution(result as int, k as int, a as int, b as int, v as int),
        exists|i: int| 1 <= i <= 127 && can_store_nuts(i, k as int, a as int, b as int, v as int) && result as int == i && 
            (forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k as int, a as int, b as int, v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed call to non-existent function by defining exec versions and adjusted invariantcasters to int */
{
    let k_int = k as i64;
    let a_int = a as i64;
    let b_int = b as i64;
    let v_int = v as i64;
    let mut result: i64 = 1;
    while result <= 127 && !can_store_nuts_exec(result, k_int, a_int, b_int, v_int)
        invariant
            result >= 1,
            forall|j: int| 1 <= j < result as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int)
        decreases 128 - (result as int)
    {
        result += 1;
    }
    proof {
        assert(result <= 127);
        assert(can_store_nuts(result as int, k as int, a as int, b as int, v as int));
    }
    result as i8
}
// </vc-code>


}

fn main() {}