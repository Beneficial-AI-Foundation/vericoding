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
/* helper modified by LLM (iteration 4): monotonicity of box_capacity when increasing boxes */
fn box_capacity_increases(n: int, k: int, b: int, v: int)
    requires
        n >= 0, 2 <= k, 1 <= v,
    ensures
        box_capacity(n + 1, k, b, v) >= box_capacity(n, k, b, v) + 1,
{
    proof {
        // k - 1 is at least 1 and n+1 >= n
        assert(k - 1 >= 1);
        assert(n + 1 >= n);

        let x0: int = (k - 1) * n;
        let x1: int = (k - 1) * (n + 1);

        // difference simplifies to k - 1 which is >= 1
        assert(x1 - x0 == (k - 1));
        assert(k - 1 >= 1);
        assert(x1 - x0 >= 1);
        assert(x1 >= x0);

        // monotonicity of min by cases
        if b <= x0 {
            assert(min(b, x0) == b);
            assert(min(b, x1) == b);
        } else if b <= x1 {
            assert(min(b, x0) == x0);
            assert(min(b, x1) == b);
            assert(b >= x0);
        } else {
            assert(min(b, x0) == x0);
            assert(min(b, x1) == x1);
        }

        let min0: int = min(b, x0);
        let min1: int = min(b, x1);
        assert(min1 >= min0);

        // expand definitions and show difference at least 1
        assert(box_capacity(n + 1, k, b, v) == v * (n + 1 + min1));
        assert(box_capacity(n, k, b, v) == v * (n + min0));
        assert(box_capacity(n + 1, k, b, v) - box_capacity(n, k, b, v) == v * (1 + (min1 - min0)));
        assert(min1 - min0 >= 0);
        assert(v >= 1);
        assert(v * (1 + (min1 - min0)) >= v * 1);
        assert(v * 1 >= 1);
        assert(box_capacity(n + 1, k, b, v) >= box_capacity(n, k, b, v) + 1);
    }
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
    /* code modified by LLM (iteration 4): search loop using i64 and bridging runtime values to spec-level predicates */
    let mut i: i8 = 1;
    while i <= 127
        invariant
            1 <= i as int,
            i as int <= 128,
            forall|j: int| 1 <= j < i as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int),
        decreases 128 - i as int
    {
        let num_boxes_i64: i64 = i as i64;
        let k_i64: i64 = k as i64;
        let b_i64: i64 = b as i64;
        let v_i64: i64 = v as i64;
        let cap_second: i64 = (k_i64 - 1) * num_boxes_i64;
        let min_val: i64 = if b_i64 <= cap_second { b_i64 } else { cap_second };
        let cap: i64 = v_i64 * (num_boxes_i64 + min_val);

        if (a as i64) <= cap {
            proof {
                let k_i: int = k as int;
                let a_i: int = a as int;
                let b_i: int = b as int;
                let v_i: int = v as int;
                let res_i: int = i as int;

                // relate runtime computed values to spec-level expressions by casting runtime -> spec
                assert(cap_second as int == (k_i - 1) * res_i);
                assert(min_val as int == min(b_i, (k_i - 1) * res_i));
                assert(cap as int == v_i * (res_i + min_val as int));

                // use the runtime comparison to conclude the spec-level predicate
                assert((a as i64) <= cap);
                assert((a as i64) as int == a_i);
                assert(a_i <= cap as int);

                assert(can_store_nuts(res_i, k_i, a_i, b_i, v_i));
                if res_i != 1 {
                    let prev: int = res_i - 1;
                    assert(!can_store_nuts(prev, k_i, a_i, b_i, v_i));
                }
            }
            return i;
        }
        i = i + 1;
    }
    127
}

// </vc-code>


}

fn main() {}