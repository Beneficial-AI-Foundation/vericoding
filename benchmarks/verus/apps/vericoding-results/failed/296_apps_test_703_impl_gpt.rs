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
proof fn lemma_min_ge_one(x: int, y: int)
    ensures
        x >= 1 && y >= 1 ==> min(x, y) >= 1,
{
    if x <= y {
        if x >= 1 && y >= 1 {
            assert(min(x, y) == x);
            assert(min(x, y) >= 1);
        }
    } else {
        if x >= 1 && y >= 1 {
            assert(min(x, y) == y);
            assert(min(x, y) >= 1);
        }
    }
}

proof fn lemma_capacity_ge_vn1(n: int, k: int, b: int, v: int)
    requires
        n >= 1,
        k >= 2,
        b >= 1,
        v >= 1,
    ensures
        box_capacity(n, k, b, v) >= v * (n + 1),
{
    let t = (k - 1) * n;
    assert(t >= 1);
    lemma_min_ge_one(b, t);
    assert(min(b, t) >= 1);
    assert(n + min(b, t) >= n + 1);
    assert(box_capacity(n, k, b, v) == v * (n + min(b, t)));
    assert(v * (n + min(b, t)) >= v * (n + 1));
}

proof fn lemma_can_store_at_a(k: int, a: int, b: int, v: int)
    requires
        valid_input(k, a, b, v),
    ensures
        can_store_nuts(a, k, a, b, v),
{
    assert(a >= 1);
    assert(k >= 2);
    assert(b >= 1);
    assert(v >= 1);
    lemma_capacity_ge_vn1(a, k, b, v);
    assert(box_capacity(a, k, b, v) >= v * (a + 1));
    assert(v * (a + 1) >= 1 * (a + 1));
    assert(1 * (a + 1) == a + 1);
    assert(a + 1 >= a);
    assert(box_capacity(a, k, b, v) >= a);
    assert(can_store_nuts(a, k, a, b, v));
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
    let mut n: i8 = 1;
    proof {
        assert(1 <= a as int);
    }
    while (n as int) < (a as int) && !can_store_nuts(n as int, k as int, a as int, b as int, v as int)
        invariant
            1 <= n as int,
            (n as int) <= a as int,
            forall|j: int| 1 <= j < n as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int),
        decreases (a as int - n as int)
    {
        let prev_n: int = n as int;
        n = n + 1;
        proof {
            assert(prev_n + 1 == n as int);
            assert forall|j: int| 1 <= j < n as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int) by {
                if j < prev_n {
                    assert(1 <= j && j < prev_n);
                    assert(!can_store_nuts(j, k as int, a as int, b as int, v as int));
                } else {
                    assert(!(j < prev_n));
                    assert(j >= prev_n);
                    assert(j < prev_n + 1);
                    assert(j <= prev_n);
                    assert(j == prev_n);
                    assert(!can_store_nuts(prev_n, k as int, a as int, b as int, v as int));
                }
            };
        }
    }
    if !can_store_nuts(n as int, k as int, a as int, b as int, v as int) {
        proof {
            assert((n as int) >= (a as int));
            assert((n as int) <= (a as int));
            assert(n as int == a as int);
            lemma_can_store_at_a(k as int, a as int, b as int, v as int);
            assert(can_store_nuts(n as int, k as int, a as int, b as int, v as int));
        }
    }
    proof {
        assert(1 <= n as int && n as int <= a as int);
        if (n as int) > 1 {
            let j: int = (n as int) - 1;
            assert(1 <= j && j < n as int);
            assert(!can_store_nuts(j, k as int, a as int, b as int, v as int));
        }
    }
    let mut result: i8 = n;
    proof {
        assert(result as int == n as int);
        assert(can_store_nuts(result as int, k as int, a as int, b as int, v as int));
        assert forall|j: int| 1 <= j < result as int ==> !can_store_nuts(j, k as int, a as int, b as int, v as int) by {
            assert(1 <= j && j < result as int);
            assert(j < n as int) by { assert(result as int == n as int); }
            assert(!can_store_nuts(j, k as int, a as int, b as int, v as int));
        };
        assert(exists|i: int|
            1 <= i && i <= 127 &&
            can_store_nuts(i, k as int, a as int, b as int, v as int) &&
            result as int == i &&
            (forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k as int, a as int, b as int, v as int))
        ) by {
            let i = result as int;
            assert(1 <= i);
            assert(i <= 127);
            assert(can_store_nuts(i, k as int, a as int, b as int, v as int));
            assert(forall|j: int| 1 <= j < i ==> !can_store_nuts(j, k as int, a as int, b as int, v as int));
        }
    }
    result
}
// </vc-code>


}

fn main() {}