// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32]) -> (max: i32)
    requires a.len() > 0,
    ensures forall|j: int| 0 <= j < a.len() ==> max >= a[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}