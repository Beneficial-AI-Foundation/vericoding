// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &[i32]) -> (r: i32)
    requires a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() ==> r <= a[i],
// </vc-spec>
// <vc-code>
{
    let mut min = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> min <= a[k],
        decreases a.len() - i
    {
        if a[i] < min {
            min = a[i];
        }
        i = i + 1;
    }
    min
}
// </vc-code>

}
fn main() {}