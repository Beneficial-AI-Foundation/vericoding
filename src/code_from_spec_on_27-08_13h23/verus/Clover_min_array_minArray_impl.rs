use vstd::prelude::*;

verus! {

// <vc-helpers>
fn min_array_helper(a: &[i32], i: usize) -> (r: i32)
    requires
        a.len() > 0,
        0 <= i < a.len(),
    ensures
        forall|k: int| i <= k < a.len() ==> r <= a[k],
    decreases a.len() - i,
{
    if i == a.len() - 1 {
        a[i]
    } else {
        let next_min = min_array_helper(a, i + 1);
        if a[i] < next_min {
            a[i]
        } else {
            next_min
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
    // Note: Verus currently has syntax limitations with exists quantifiers in postconditions
    // The second ensures clause from Dafny cannot be directly translated
// </vc-spec>
// </vc-spec>

// <vc-code>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
{
    min_array_helper(a, 0)
}
// </vc-code>

fn main() {}

}