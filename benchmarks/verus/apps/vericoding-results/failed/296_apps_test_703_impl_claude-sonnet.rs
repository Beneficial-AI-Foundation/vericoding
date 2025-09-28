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
/* helper modified by LLM (iteration 5): fixed integer literal types for proper int arithmetic */
fn lemma_box_capacity_monotonic(num_boxes1: int, num_boxes2: int, k: int, b: int, v: int)
    requires
        0 <= num_boxes1 <= num_boxes2,
        k >= 2,
        b >= 1,
        v >= 1
    ensures
        box_capacity(num_boxes1, k, b, v) <= box_capacity(num_boxes2, k, b, v)
{
    let diff = num_boxes2 - num_boxes1;
    assert(min(b, (k - 1) * num_boxes1) <= min(b, (k - 1) * num_boxes2));
}

fn lemma_box_capacity_positive(num_boxes: int, k: int, b: int, v: int)
    requires
        num_boxes >= 1,
        k >= 2,
        b >= 1,
        v >= 1
    ensures
        box_capacity(num_boxes, k, b, v) >= v
{
    assert(min(b, (k - 1) * num_boxes) >= 0);
}

fn lemma_search_bound(k: int, a: int, b: int, v: int)
    requires
        valid_input(k, a, b, v)
    ensures
        exists|i: int| 1 <= i <= 127 && can_store_nuts(i, k, a, b, v)
{
    let upper_bound = (a + v - 1) / v;
    assert(upper_bound >= 1);
    if upper_bound <= 127 {
        assert(can_store_nuts(upper_bound, k, a, b, v));
    } else {
        assert(can_store_nuts(127, k, a, b, v));
    }
}

fn lemma_can_store_nuts_exec(num_boxes: i8, k: i8, a: i8, b: i8, v: i8) -> (result: bool)
    requires
        1 <= num_boxes <= 127,
        valid_input(k as int, a as int, b as int, v as int)
    ensures
        result == can_store_nuts(num_boxes as int, k as int, a as int, b as int, v as int)
{
    let capacity = v * (num_boxes + if b <= (k - 1) * num_boxes { b } else { (k - 1) * num_boxes });
    a <= capacity
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
{
    /* code modified by LLM (iteration 5): use executable helper function instead of spec function in loop condition */
    let mut num_boxes = 1i8;
    
    proof {
        lemma_search_bound(k as int, a as int, b as int, v as int);
    }
    
    while !lemma_can_store_nuts_exec(num_boxes, k, a, b, v)
        invariant
            1 <= num_boxes <= 127,
            forall|j: int| 1 <= j < num_boxes ==> !can_store_nuts(j, k as int, a as int, b as int, v as int)
        decreases 127 - num_boxes
    {
        proof {
            lemma_box_capacity_monotonic(num_boxes as int, (num_boxes + 1) as int, k as int, b as int, v as int);
        }
        num_boxes = num_boxes + 1;
    }
    
    proof {
        assert(can_store_nuts(num_boxes as int, k as int, a as int, b as int, v as int));
        assert(num_boxes == 1 || !can_store_nuts((num_boxes - 1) as int, k as int, a as int, b as int, v as int));
        assert(is_minimal_solution(num_boxes as int, k as int, a as int, b as int, v as int));
    }
    
    num_boxes
}
// </vc-code>


}

fn main() {}