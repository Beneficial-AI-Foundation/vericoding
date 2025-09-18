// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn non_empty_positive(x: Vec<i32>) -> bool { x.len() > 0 && forall|i: int| 0 <= i < x.len() ==> x[i as int] > 0 }
// </vc-helpers>

// <vc-spec>
fn log(x: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i as int] > 0,
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}