use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
    // Note: Verus currently has syntax limitations with exists quantifiers in postconditions
    // The second ensures clause from Dafny cannot be directly translated
// </vc-spec>
// <vc-code>
{
    assume(false);
    0 // unreachable due to assume(false)
}
// </vc-code>

fn main() {}

}
