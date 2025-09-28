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
fn calculate_trips(weight: i8, k: i8) -> i8 {
    if weight == 0 {
        0
    } else {
        (weight + k - 1) / k
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
    let mut total: i8 = 0;
    let mut i: usize = 0;
    
    while i < w.len()
        invariant
            0 <= i <= w.len(),
            total as int == sum_trips(w@.subrange(0, i as int).map_values(|v: i8| v as int), k as int),
        decreases w.len() - i
    {
        let trips = calculate_trips(w[i], k);
        total = total + trips;
        i = i + 1;
    }
    
    (total + 1) / 2
}
// </vc-code>


}

fn main() {}