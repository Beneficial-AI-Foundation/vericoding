// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sqr_sum_rec(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 { 0 } else { n*n + sqr_sum_rec(n-1) }
}

proof fn l1(n: int)
    requires n >= 0
    ensures sqr_sum_rec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sqr_sum1(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_rec(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}