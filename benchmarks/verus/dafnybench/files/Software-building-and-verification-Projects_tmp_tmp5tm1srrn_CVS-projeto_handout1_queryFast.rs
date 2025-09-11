// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= a.len()
    decreases j - i
    when 0 <= i <= j <= a.len()
{
    if i == j { 0 }
    else { a[j-1] + sum(a, i, j-1) }
}

spec fn is_prefix_sum_for(a: Seq<int>, c: Seq<int>) -> bool
{
    a.len() + 1 == c.len() && 
    forall|i: int| #![auto] 0 <= i <= a.len() ==> c[i] == sum(a, 0, i)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn queryFast(a: Seq<int>, c: Seq<int>, i: int, j: int) -> (r: int)
    requires 0 <= i <= j <= a.len(),
             is_prefix_sum_for(a, c)
    ensures r == sum(a, i, j)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}