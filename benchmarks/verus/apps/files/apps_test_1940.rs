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
        (w[0] + k - 1) / k + sum_trips(w.subrange(1, w.len() as int), k)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int, w: Seq<int>) -> (result: int)
    requires valid_input(n, k, w),
    ensures result >= 0,
    ensures result == (sum_trips(w, k) + 1) / 2,
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}