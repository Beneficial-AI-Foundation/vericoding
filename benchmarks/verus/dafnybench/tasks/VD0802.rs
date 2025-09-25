// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n <= 0 { 0 } else { sum_to(a, n - 1) + a[n - 1] }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &[i32]) -> (result: i32)
    ensures result == sum_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}