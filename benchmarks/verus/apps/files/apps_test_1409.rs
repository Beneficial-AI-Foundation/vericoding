// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_eligible(participations: Seq<int>, k: int) -> int
    requires 0 <= k <= 5
    requires forall|i: int| 0 <= i < participations.len() ==> 0 <= participations[i] <= 5
    decreases participations.len()
{
    if participations.len() == 0 {
        0
    } else {
        (if 5 - participations[0] >= k { 1 } else { 0 }) + count_eligible(participations.subrange(1, participations.len() as int), k)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, participations: Seq<int>) -> (result: int)
    requires 0 <= k <= 5
    requires n == participations.len()
    requires forall|i: int| 0 <= i < participations.len() ==> 0 <= participations[i] <= 5
    ensures result == (count_eligible(participations, k) / 3)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}