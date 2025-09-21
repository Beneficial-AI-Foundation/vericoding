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
fn percentile(p: i8, a: &[i8], total: i8) -> (i: i32)
    requires 
        forall|idx: int| 0 <= idx < a.len() ==> a@[idx] as int > 0,
        0 <= p as int <= 100,
        total as int == sum(a@.map(|i: int, x: i8| x as int)),
        total as int > 0,
    ensures 
        -1 <= i < a.len(),
        sum_upto(a@.map(|i: int, x: i8| x as int), i as int) <= (p as int * total as int) / 100,
        i as int + 1 < a.len() ==> sum_upto(a@.map(|i: int, x: i8| x as int), i as int + 1) > (p as int * total as int) / 100,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}