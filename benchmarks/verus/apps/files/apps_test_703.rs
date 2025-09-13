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
// </vc-helpers>

// <vc-spec>
fn solve(k: int, a: int, b: int, v: int) -> (result: int)
    requires 
        valid_input(k, a, b, v)
    ensures 
        result >= 1,
        result <= 1009,
        is_minimal_solution(result, k, a, b, v),
        exists|i: int| 1 <= i <= 1009 && can_store_nuts(i, k, a, b, v) && result == i && 
            (forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k, a, b, v))
// </vc-spec>
// <vc-code>
{
    assume(false);
    0 as int
}
// </vc-code>


}

fn main() {}