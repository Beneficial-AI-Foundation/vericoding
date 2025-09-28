// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, w: Seq<int>) -> bool {
    k > 0 && n >= 0 && w.len() == n && forall|i: int| 0 <= i < w.len() ==> w[i] >= 0
}

spec fn sum_trips(w: Seq<int>, k: int) -> int
    decreases w.len()
{
    if w.len() == 0 {
        0
    } else {
        (w[0] + k - 1) / k + sum_trips(w.drop_first(), k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified bound lemma and added division bound helper */
proof fn sum_trips_monotonic(w: Seq<int>, k: int)
    requires
        k > 0,
        forall|i: int| 0 <= i < w.len() ==> w[i] >= 0,
    ensures
        sum_trips(w, k) >= 0,
    decreases w.len()
{
    if w.len() == 0 {
    } else {
        sum_trips_monotonic(w.drop_first(), k);
    }
}

proof fn division_bound(x: int, k: int)
    requires
        k > 0,
        x >= 0,
        x <= 127,
    ensures
        (x + k - 1) / k <= 127,
{
    if k == 1 {
        assert((x + k - 1) / k == x);
    } else {
        assert((x + k - 1) / k <= (127 + k - 1) / k);
        assert((127 + k - 1) / k <= (127 + 127 - 1) / k);
        assert((127 + 127 - 1) / k <= 253 / 2);
        assert(253 / 2 <= 126);
    }
}

proof fn sum_trips_bound(w: Seq<int>, k: int)
    requires
        k > 0,
        forall|i: int| 0 <= i < w.len() ==> w[i] >= 0,
        w.len() <= 127,
        forall|i: int| 0 <= i < w.len() ==> w[i] <= 127,
    ensures
        sum_trips(w, k) <= 127 * w.len(),
    decreases w.len()
{
    if w.len() == 0 {
    } else {
        division_bound(w[0], k);
        sum_trips_bound(w.drop_first(), k);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, w: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, w@.map_values(|v: i8| v as int)),
    ensures 
        result >= 0,
        result as int == (sum_trips(w@.map_values(|v: i8| v as int), k as int) + 1) / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type conversions and overflow handling */
    let mut total = 0i8;
    let mut i = 0;
    
    proof {
        sum_trips_monotonic(w@.map_values(|v: i8| v as int), k as int);
        sum_trips_bound(w@.map_values(|v: i8| v as int), k as int);
    }
    
    while i < w.len()
        invariant
            0 <= i <= w.len(),
            total >= 0,
            total as int == sum_trips(w@.map_values(|v: i8| v as int).subrange(0, i as int), k as int),
            total <= 127,
        decreases w.len() - i
    {
        let weight = w[i];
        assert(weight >= 0);
        let weight_plus_k_minus_1 = weight + k - 1;
        assert(weight_plus_k_minus_1 >= 0);
        let trips = weight_plus_k_minus_1 / k;
        assert(trips >= 0);
        proof {
            division_bound(weight as int, k as int);
        }
        assert(trips <= 127);
        assert(total + trips <= 254);
        total = total + trips;
        i = i + 1;
    }
    
    assert(total <= 127);
    assert(total >= 0);
    assert(total / 2 >= 0);
    total / 2
}
// </vc-code>


}

fn main() {}