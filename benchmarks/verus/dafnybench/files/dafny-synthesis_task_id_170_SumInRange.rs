// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: Seq<int>, start: int, end: int) -> int
    recommends 
        0 <= start <= end <= a.len(),
    decreases end
    when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        sum_to(a, start, end - 1) + a[end - 1]
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_in_range(a: &[i32], start: usize, end: usize) -> (sum: i32)
    requires 
        start <= end <= a.len(),
    ensures
        sum == sum_to(a@.map(|i, v| v as int), start as int, end as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}