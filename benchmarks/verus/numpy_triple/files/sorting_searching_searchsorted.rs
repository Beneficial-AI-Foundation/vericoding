// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_searchsorted(a: Vec<i8>, v: Vec<i8>) -> (result: Vec<usize>)
    requires 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] as int <= a[j] as int,
    ensures 
        result.len() == v.len()
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}