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
proof fn lemma_sum_trips_nonnegative(w: Seq<int>, k: int)
    requires
        k > 0,
        w.len() >= 0,
        forall|i: int| 0 <= i < w.len() ==> w[i] >= 0,
    ensures
        sum_trips(w, k) >= 0,
decreases w.len(),
{
    if w.len() == 0 {
        // Base case: empty sequence has sum 0, which is >= 0
    } else {
        assert(w[0] >= 0);
        lemma_ceil_properties(w[0], k);
        lemma_sum_trips_nonnegative(w.drop_first(), k);
    }
}

proof fn lemma_ceil_properties(a: int, d: int)
    requires
        a >= 0,
        d > 0,
    ensures
        (a + d - 1) / d >= 0,
        (a + d - 1) / d >= a / d,
{
    assert((a + d - 1) / d >= a / d);
    assert(a / d >= 0);
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
    /* code modified by LLM (iteration 5): Fixed type conversion error in take() method argument */
    proof {
        lemma_sum_trips_nonnegative(w@.map_values(|v: i8| v as int), k as int);
    }
    
    let mut total_trips: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            i <= w@.len(),
            total_trips >= 0,
            total_trips as int == sum_trips(w@.take(i as int).map_values(|v: i8| v as int), k as int),
        decreases n as int - i as int,
    {
        let weight = w[i];
        total_trips += ((weight as i32 + k as i32 - 1) / k as i32) as i8;
        i += 1;
    }
    
    ((total_trips + 1) / 2) as i8
}
// </vc-code>


}

fn main() {}