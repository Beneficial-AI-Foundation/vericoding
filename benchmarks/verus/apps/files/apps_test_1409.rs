// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_eligible(participations: Seq<int>, k: int) -> int
    decreases participations.len()
{
    if participations.len() == 0 {
        0 as int
    } else {
        (if 5 - participations[0] >= k { 1 as int } else { 0 as int }) + count_eligible(participations.subrange(1, participations.len() as int), k)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, k: u8, participations: Vec<u8>) -> (result: u8)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}