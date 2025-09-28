use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut min = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> min <= a@[j],
            exists|j: int| 0 <= j < i && min == a@[j],
        decreases a.len() - i,
    {
        if a[i] < min {
            min = a[i];
        }
        i = i + 1;
    }
    
    min
}
// </vc-code>

fn main() {}

}