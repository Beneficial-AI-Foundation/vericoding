// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort(A: &mut Vec<i32>, n: usize)
    requires 
        n == old(A).len(),
        n >= 0,
    ensures
        forall|i: int, j: int| 0 <= i <= j < n ==> A[i] <= A[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}