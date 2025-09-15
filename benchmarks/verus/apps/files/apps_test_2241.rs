// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_contributions(a: Seq<int>, b: Seq<int>) -> int
    recommends a.len() == b.len()
    decreases a.len()
{
    if a.len() == 0 { 
        0
    } else {
        (if b[0] > 1 && 2 * a[0] >= b[0] {
            let x = b[0] / 2;
            let y = b[0] - x;
            x * y
         } else { 
             -1 
         }) + sum_contributions(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: Seq<int>, b: Seq<int>) -> (result: int)
    requires a.len() == b.len()
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}