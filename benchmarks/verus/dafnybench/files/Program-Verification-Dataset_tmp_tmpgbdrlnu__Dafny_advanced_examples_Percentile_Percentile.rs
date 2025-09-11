// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_upto(a: Seq<int>, end: int) -> int
    decreases end + 2
{
    if end < 0 {
        0
    } else if end >= a.len() {
        0
    } else {
        a[end] + sum_upto(a, end - 1)
    }
}

spec fn sum(a: Seq<int>) -> int {
    sum_upto(a, a.len() - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn percentile(p: int, a: &[int], total: int) -> (i: i32)
    requires 
        forall|idx: int| 0 <= idx < a.len() ==> a@[idx] > 0,
        0 <= p <= 100,
        total == sum(a@),
        total > 0,
    ensures 
        -1 <= i < a.len(),
        sum_upto(a@, i as int) <= (p * total) / 100,
        i as int + 1 < a.len() ==> sum_upto(a@, i as int + 1) > (p * total) / 100,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}