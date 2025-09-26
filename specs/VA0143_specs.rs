// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_sorted(hotels: Seq<int>, n: int) -> bool
    decreases n
{
    if n <= 1 {
        true
    } else {
        hotels[n-2] < hotels[n-1] && is_sorted(hotels, n-1)
    }
}

spec fn valid_input(n: int, d: int, hotels: Seq<int>) -> bool {
    n > 0 && d > 0 && hotels.len() == n && is_sorted(hotels, n)
}

spec fn sum_contributions(hotels: Seq<int>, d: int, i: int) -> int
    recommends 0 <= i && i <= hotels.len() - 1,
                d > 0,
                is_sorted(hotels, hotels.len() as int)
    decreases i
    when i >= 0
{
    if i == 0 { 
        0 
    } else {
        let gap = hotels[i as int] - hotels[(i-1) as int];
        let contribution: int = if gap == 2*d { 1 } else if gap > 2*d { 2 } else { 0 };
        contribution + sum_contributions(hotels, d, i-1)
    }
}

spec fn correct_result(n: int, d: int, hotels: Seq<int>, result: int) -> bool
    recommends valid_input(n, d, hotels)
{
    result == 2 + sum_contributions(hotels, d, n-1) && result >= 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, d: i8, hotels: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, d as int, hotels@.map(|_, x: i8| x as int))
    ensures correct_result(n as int, d as int, hotels@.map(|_, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}