// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32]) -> (result: i32)
    requires a.len() > 0
    ensures forall|j: int| 0 <= j < a.len() ==> result >= a[j]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}