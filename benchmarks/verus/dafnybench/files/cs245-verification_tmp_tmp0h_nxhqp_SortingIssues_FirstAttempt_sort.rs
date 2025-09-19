// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sort(A: &mut Vec<i8>, n: usize)
    requires 
        n == old(A).len(),
        n >= 0,
    ensures
        forall|i: int, j: int| 0 <= i <= j < n ==> A[i] as int <= A[j] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}