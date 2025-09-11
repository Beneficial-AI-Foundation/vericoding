// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn quicksort_partition(x: &mut Vec<i32>, n: usize, p: i32) -> (result: (usize, usize))
    requires old(x).len() >= 1, n == old(x).len()
    ensures 
        result.1 >= n,
        forall|i: int| 0 <= i < (result.0 as int) && (result.0 as int) < (n as int) ==> x[i] <= p,
        result.0 == n || (forall|i: int| (result.0 as int) <= i && i < (n as int) ==> x[i] > p),
        x@.to_multiset() == old(x)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}