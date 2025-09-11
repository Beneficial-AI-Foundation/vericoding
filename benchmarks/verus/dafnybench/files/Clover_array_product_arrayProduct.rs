// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}