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
/* helper modified by LLM (iteration 5): Add type annotation to fix compilation error */
fn lemma_min_boundary(a: int, b: int)
    ensures
        min(a, b) <= a,
        min(a, b) <= b
{
}

proof fn lemma_box_capacity_monotonic(k: int, b: int, v: int, n1: int, n2: int)
    requires
        n1 >= 0,
        n2 >= 0,
        n1 <= n2,
        2 <= k <= 1000,
        1 <= b <= 1000,
        1 <= v <= 1000
    ensures
        box_capacity(n1, k, b, v) <= box_capacity(n2, k, b, v)
{
}

proof fn lemma_can_store_nuts_monotonic(k: int, a: int, b: int, v: int, n1: int, n2: int)
    requires
        n1 >= 0,
        n2 >= 0,
        n1 <= n2,
        valid_input(k, a, b, v)
    ensures
        can_store_nuts(n1, k, a, b, v) ==> can_store_nuts(n2, k, a, b, v)
{
    lemma_box_capacity_monotonic(k, b, v, n1, n2);
}

proof fn find_min_solution(k: int, a: int, b: int, v: int) -> (result: int)
    requires
        valid_input(k, a, b, v),
        exists|i: int| 1 <= i <= 127 && can_store_nuts(i, k, a, b, v)
    ensures
        result >= 1,
        result <= 127,
        is_minimal_solution(result, k, a, b, v)
{
    let mut n: int = 1;
    while n <= 127 && !can_store_nuts(n, k, a, b, v)
        invariant
            1 <= n <= 128,
            forall|j: int| 1 <= j < n ==> !can_store_nuts(j, k, a, b, v),
            exists|i: int| n <= i <= 127 && can_store_nuts(i, k, a, b, v)
        decreases 128 - n
    {
        n = n + 1;
    }
    n
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
/* code modified by LLM (iteration 5): Fix while loop condition and verification */
{
    let mut current: i8 = 1;
    while current <= 127 && !can_store_nuts(current as int, k as int, a as int, b as int, v as int)
        invariant
            1 <= current <= 128,
            forall|j: int| 1 <= j < current as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int)
        decreases 128 - current
    {
        current = current + 1;
    }
    
    current
}
// </vc-code>


}

fn main() {}