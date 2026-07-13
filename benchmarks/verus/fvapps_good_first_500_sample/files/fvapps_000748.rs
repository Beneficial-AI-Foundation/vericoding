// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum(xs: Seq<nat>) -> nat 
    decreases xs.len()
{
    if xs.len() == 0 {
        0
    } else {
        xs[0] + sum(xs.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn find_min_event_time(n: nat, times: Vec<Vec<nat>>) -> (result: nat)
    requires 
        n == times.len(),
        forall|i: int| 0 <= i < times.len() ==> times[i].len() == 3,
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result = find_min_event_time(3, vec![vec![18, 7, 6], vec![23, 10, 27], vec![20, 9, 14]]);
    // println!("Result: {}", result);
}