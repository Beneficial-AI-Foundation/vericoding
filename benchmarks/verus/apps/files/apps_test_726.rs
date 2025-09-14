// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, d: int, hotels: Seq<int>) -> bool {
    n > 0 && d > 0 && hotels.len() == n &&
    (forall|i: int| 0 <= i < n - 1 ==> hotels[i] < hotels[i + 1])
}

spec fn sum_contributions(hotels: Seq<int>, d: int, i: int) -> int
    decreases i
{
    if 0 <= i <= hotels.len() - 1 && d > 0 &&
       (forall|j: int| 0 <= j < hotels.len() - 1 ==> hotels[j] < hotels[j + 1]) {
        if i == 0 { 0 }
        else {
            let gap = hotels[i] - hotels[i-1];
            let contribution: int = if gap == 2*d { 1 } else if gap > 2*d { 2 } else { 0 };
            contribution + sum_contributions(hotels, d, i-1)
        }
    } else {
        0
    }
}

spec fn correct_result(n: int, d: int, hotels: Seq<int>, result: int) -> bool {
    valid_input(n, d, hotels) ==> 
    (result == 2 + sum_contributions(hotels, d, n-1) && result >= 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, d: int, hotels: Seq<int>) -> (result: int)
    requires valid_input(n, d, hotels)
    ensures correct_result(n, d, hotels, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}